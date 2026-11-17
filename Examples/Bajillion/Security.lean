module

public import DY.Trace.ReachabilityTheorem
public import DY.Actions.ProtocolEvent

namespace DY.Example.Bajillion

open DY

public section

/-- A signed payment acknowledgement.  The endpoint consists of the payer's
epoch-local sequence, cumulative debit, recipient, recipient cumulative amount
and recipient payment count. -/
structure Ack where
  payer : Nat
  seq : Nat
  debit : Nat
  recipient : Nat
  cumulative : Nat
  count : Nat
  context : Nat
  payerSig : Bool
  operatorSig : Bool
deriving DecidableEq, Repr

/-- The public close committed by the operator and certified by the committee. -/
structure Close where
  payer : Nat
  seq : Nat
  recipient : Nat
  rowDebit : Nat
  tipCumulative : Nat
  tipCount : Nat
  context : Nat
  valid : Bool
deriving DecidableEq, Repr

/-- Events visible in the symbolic trace. -/
inductive Event where
  | ack (a : Ack)
  | close (c : Close)
deriving DecidableEq, Repr

namespace Ack

def valid (a : Ack) : Prop :=
  a.payerSig = true ∧ a.operatorSig = true

def matchesClose (a : Ack) (c : Close) : Prop :=
  a.payer = c.payer ∧ a.seq = c.seq ∧ a.context = c.context

def matchesEntry (a : Ack) (c : Close) : Prop :=
  a.matchesClose c ∧ a.recipient = c.recipient

def sameEndpoint (a b : Ack) : Prop :=
  a.debit = b.debit ∧
  a.cumulative = b.cumulative ∧
  a.count = b.count ∧
  a.recipient = b.recipient

end Ack

instance : ExecTraceTypes where
  ExecT := ProtocolEvent.ExecEntryT Event

instance : ProofTraceTypes where
  ProofT := ProtocolEvent.ProofEntryT Event

instance : ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Event) :=
  inferInstanceAs (ExecTraceTypes.Has ExecTrace.Entry)

instance : ProofTraceTypes.Has (ProtocolEvent.ProofEntryT Event) :=
  inferInstanceAs (ProofTraceTypes.Has ProofTrace.Entry)

/-- A close dominates every earlier matching acknowledgement.  This is the
trace invariant that makes the three arithmetic challenge arms sound. -/
def CloseDominates (tr : ProofTrace) (c : Close) : Prop :=
  ∀ i, i < tr.length → ∀ a : Ack,
    tr.erase.at? i = some (ProtocolEvent.ExecEntryT.mk (Event.ack a)) →
    a.payer = c.payer →
    a.seq = c.seq →
    a.context = c.context →
      c.rowDebit ≥ a.debit ∧
      c.tipCumulative ≥ a.cumulative ∧
      c.tipCount ≥ a.count

/-- The operator never signs two different endpoints for the same `(payer, seq)`.
This is the assumption used by the fork arm. -/
def NoConflictingAcks (tr : ProofTrace) : Prop :=
  ∀ i j a b,
    tr.erase.EventLoggedAt (Event.ack a) i →
    tr.erase.EventLoggedAt (Event.ack b) j →
    a.payer = b.payer →
    a.seq = b.seq →
    Ack.sameEndpoint a b

instance : ProtocolEvent.EventInv Event where
  invariant tr ev :=
    match ev with
    | .ack a => Ack.valid a
    | .close c => c.valid = true ∧ CloseDominates tr c

instance : TraceInvariant where
  tc_inv := inferInstanceAs (SubTraceInvariant (ProtocolEvent.ProofEntryT Event))

instance : TraceInvariant.Has (ProtocolEvent.ProofEntryT Event) :=
  inferInstanceAs (TraceInvariant.Has ProofTrace.Entry)

/-- The three challenge arms described in the protocol document. -/
inductive ChallengeKind where
  | higherDebit
  | higherEntry
  | fork
deriving DecidableEq, Repr

inductive Verdict where
  | proven (kind : ChallengeKind)
  | noContradiction
  | invalidEvidence
deriving DecidableEq, Repr

inductive Challenge where
  | higherDebit (ack : Ack)
  | higherEntry (ack : Ack)
  | fork (left right : Ack)
deriving DecidableEq, Repr

open Classical

/-- The chain-side checker.  It returns `proven` only when the authenticated
acknowledgement strictly exceeds the close's committed value. -/
noncomputable def check (c : Close) : Challenge → Verdict
  | .higherDebit a =>
      if a.valid ∧ a.matchesClose c ∧ a.debit > c.rowDebit then
        .proven .higherDebit
      else
        .noContradiction
  | .higherEntry a =>
      if a.valid ∧ a.matchesEntry c ∧
          (a.cumulative > c.tipCumulative ∨ a.count > c.tipCount) then
        .proven .higherEntry
      else
        .noContradiction
  | .fork l r =>
      if l.operatorSig = true ∧ r.operatorSig = true ∧
          l.context = c.context ∧ r.context = c.context ∧
          l.payer = r.payer ∧ l.seq = r.seq ∧
          ¬ Ack.sameEndpoint l r then
        .proven .fork
      else
        .noContradiction

/-- If an acknowledgement is logged, its event invariant holds. -/
theorem ack_invariant_of_logged
  (tr : ProofTrace) (a : Ack) (i : Nat)
  (h_inv : tr.Invariant)
  (h_ack : tr.erase.EventLoggedAt (Event.ack a) i)
  : Ack.valid a
:= by
  have h := Trace.EventLoggedAt_imp_EventInv (Event.ack a) i tr h_inv h_ack
  simpa [ProtocolEvent.EventInv.invariant] using h

/-- If a close is logged, its event invariant holds. -/
theorem close_invariant_of_logged
  (tr : ProofTrace) (c : Close) (j : Nat)
  (h_inv : tr.Invariant)
  (h_close : tr.erase.EventLoggedAt (Event.close c) j)
  : c.valid = true ∧ CloseDominates (tr.prefix j) c
:= by
  have h := Trace.EventLoggedAt_imp_EventInv (Event.close c) j tr h_inv h_close
  simpa [ProtocolEvent.EventInv.invariant] using h

/-- A close logged at `j` dominates every matching acknowledgement logged
before `j`. -/
theorem close_dominates_ack
  (tr : ProofTrace) (c : Close) (a : Ack) (i j : Nat)
  (h_inv : tr.Invariant)
  (h_ack : tr.erase.EventLoggedAt (Event.ack a) i)
  (h_close : tr.erase.EventLoggedAt (Event.close c) j)
  (h_ij : i < j)
  (h_payer : a.payer = c.payer)
  (h_seq : a.seq = c.seq)
  (h_context : a.context = c.context)
  : c.rowDebit ≥ a.debit ∧
    c.tipCumulative ≥ a.cumulative ∧
    c.tipCount ≥ a.count
:= by
  have h_close_inv := close_invariant_of_logged tr c j h_inv h_close
  have h_dom := h_close_inv.2
  have h_i_len : i < tr.erase.length :=
    Trace.EventLoggedAt_implies_i_le_length (Event.ack a) i tr.erase h_ack
  have h_i_tr : i < tr.length := by simpa [Trace.erase_length] using h_i_len
  have h_ack_prefix : (tr.prefix j).erase.EventLoggedAt (Event.ack a) i := by
    have h_len : i < (tr.erase.prefix j).length := by
      rw [Trace.prefix_length]
      omega
    have h_le : tr.erase.prefix j ≤ tr.erase := Trace.prefix_le_self tr.erase j
    have h' := Trace.EventLoggedAt_le' (Event.ack a) i (tr.erase.prefix j) tr.erase h_len h_le h_ack
    simpa [Trace.prefix_erase] using h'
  have h_at : (tr.prefix j).erase.at? i = some (ProtocolEvent.ExecEntryT.mk (Event.ack a)) := by
    simpa [Trace.EventLoggedAt] using h_ack_prefix
  exact h_dom i (by rw [Trace.prefix_length]; omega) a h_at h_payer h_seq h_context

/-- Higher-debit arm is sound for an honest close. -/
theorem higher_debit_sound
  (tr : ProofTrace) (c : Close) (a : Ack) (i j : Nat)
  (h_inv : tr.Invariant)
  (h_ack : tr.erase.EventLoggedAt (Event.ack a) i)
  (h_close : tr.erase.EventLoggedAt (Event.close c) j)
  (h_ij : i < j)
  (h_payer : a.payer = c.payer)
  (h_seq : a.seq = c.seq)
  (h_context : a.context = c.context)
  : check c (.higherDebit a) ≠ .proven .higherDebit
:= by
  have h_dom := close_dominates_ack tr c a i j h_inv h_ack h_close h_ij h_payer h_seq h_context
  have h_valid := ack_invariant_of_logged tr a i h_inv h_ack
  have h_not : ¬ (a.valid ∧ a.matchesClose c ∧ a.debit > c.rowDebit) := by
    rintro ⟨_, _, h_gt⟩
    omega
  simp [check, h_not]

/-- Higher-entry arm is sound for an honest close. -/
theorem higher_entry_sound
  (tr : ProofTrace) (c : Close) (a : Ack) (i j : Nat)
  (h_inv : tr.Invariant)
  (h_ack : tr.erase.EventLoggedAt (Event.ack a) i)
  (h_close : tr.erase.EventLoggedAt (Event.close c) j)
  (h_ij : i < j)
  (h_payer : a.payer = c.payer)
  (h_seq : a.seq = c.seq)
  (h_context : a.context = c.context)
  (h_recipient : a.recipient = c.recipient)
  : check c (.higherEntry a) ≠ .proven .higherEntry
:= by
  have h_dom := close_dominates_ack tr c a i j h_inv h_ack h_close h_ij h_payer h_seq h_context
  have h_valid := ack_invariant_of_logged tr a i h_inv h_ack
  have h_not : ¬ (a.valid ∧ a.matchesEntry c ∧
      (a.cumulative > c.tipCumulative ∨ a.count > c.tipCount)) := by
    rintro ⟨_, _, h_gt | h_gt⟩ <;> omega
  simp [check, h_not]

/-- Fork arm is sound when the operator has not equivocated. -/
theorem fork_sound
  (tr : ProofTrace) (c : Close) (l r : Ack) (i j : Nat)
  (h_no_fork : NoConflictingAcks tr)
  (h_left : tr.erase.EventLoggedAt (Event.ack l) i)
  (h_right : tr.erase.EventLoggedAt (Event.ack r) j)
  (h_payer : l.payer = r.payer)
  (h_seq : l.seq = r.seq)
  : check c (.fork l r) ≠ .proven .fork
:= by
  have h_same := h_no_fork i j l r h_left h_right h_payer h_seq
  have h_not : ¬ (l.operatorSig = true ∧ r.operatorSig = true ∧
      l.context = c.context ∧ r.context = c.context ∧
      l.payer = r.payer ∧ l.seq = r.seq ∧
      ¬ Ack.sameEndpoint l r) := by
    rintro ⟨_, _, _, _, _, _, h_neq⟩
    exact h_neq h_same
  simp [check, h_not]

/-- Combined soundness: no supported challenge convicts an honest close. -/
theorem receipt_challenge_sound
  (tr : ProofTrace) (c : Close) (ch : Challenge)
  (h_inv : tr.Invariant)
  (h_no_fork : NoConflictingAcks tr)
  (h_supported : match ch with
    | .higherDebit a =>
        ∃ i j, tr.erase.EventLoggedAt (Event.ack a) i ∧
          tr.erase.EventLoggedAt (Event.close c) j ∧ i < j ∧
          a.payer = c.payer ∧ a.seq = c.seq ∧ a.context = c.context
    | .higherEntry a =>
        ∃ i j, tr.erase.EventLoggedAt (Event.ack a) i ∧
          tr.erase.EventLoggedAt (Event.close c) j ∧ i < j ∧
          a.payer = c.payer ∧ a.seq = c.seq ∧ a.context = c.context ∧
          a.recipient = c.recipient
    | .fork l r =>
        (∃ i, tr.erase.EventLoggedAt (Event.ack l) i) ∧
        (∃ j, tr.erase.EventLoggedAt (Event.ack r) j) ∧
        l.payer = r.payer ∧ l.seq = r.seq)
  : check c ch ≠ .proven (match ch with
      | .higherDebit _ => .higherDebit
      | .higherEntry _ => .higherEntry
      | .fork _ _ => .fork)
:= by
  cases ch with
  | higherDebit a =>
      obtain ⟨i, j, h_ack, h_close, h_ij, h_payer, h_seq, h_context⟩ := h_supported
      simpa using higher_debit_sound tr c a i j h_inv h_ack h_close h_ij h_payer h_seq h_context
  | higherEntry a =>
      obtain ⟨i, j, h_ack, h_close, h_ij, h_payer, h_seq, h_context, h_recipient⟩ := h_supported
      simpa using higher_entry_sound tr c a i j h_inv h_ack h_close h_ij h_payer h_seq h_context h_recipient
  | fork l r =>
      obtain ⟨⟨i, h_left⟩, ⟨j, h_right⟩, h_payer, h_seq⟩ := h_supported
      simpa using fork_sound tr c l r i j h_no_fork h_left h_right h_payer h_seq

/-- Detection for the higher-debit arm. -/
theorem higher_debit_detects
  (c : Close) (a : Ack)
  (h_valid : a.valid)
  (h_match : a.matchesClose c)
  (h_gt : a.debit > c.rowDebit)
  : check c (.higherDebit a) = .proven .higherDebit
:= by
  simp [check, h_valid, h_match, h_gt]

/-- Detection for the higher-entry arm. -/
theorem higher_entry_detects
  (c : Close) (a : Ack)
  (h_valid : a.valid)
  (h_match : a.matchesEntry c)
  (h_gt : a.cumulative > c.tipCumulative ∨ a.count > c.tipCount)
  : check c (.higherEntry a) = .proven .higherEntry
:= by
  simp [check, h_valid, h_match, h_gt]

/-- Detection for the fork arm. -/
theorem fork_detects
  (c : Close) (l r : Ack)
  (h_l_sig : l.operatorSig = true)
  (h_r_sig : r.operatorSig = true)
  (h_l_ctx : l.context = c.context)
  (h_r_ctx : r.context = c.context)
  (h_payer : l.payer = r.payer)
  (h_seq : l.seq = r.seq)
  (h_diff : ¬ Ack.sameEndpoint l r)
  : check c (.fork l r) = .proven .fork
:= by
  simp [check, h_l_sig, h_r_sig, h_l_ctx, h_r_ctx, h_payer, h_seq, h_diff]

end

end DY.Example.Bajillion
