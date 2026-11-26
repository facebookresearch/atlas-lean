/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Linearizability
import Mathlib.Data.Nat.Find

/-!
# Finite concurrent histories

This is the event model of Herlihy and Wing, §2.1 and the real-time order of §2.2. Matching
uses the process and object, not an operation name on the response. In a well-formed history,
the events of each process alternate between invocations and their matching responses, with
a possible final pending invocation. An operation is identified by its positions in the
original history, even if another operation has identical event labels.

The bridge to `Linearizability.OpRec` forgets the process and encodes the payloads. It preserves
positions and real-time order, not process-subhistory equivalence. Neither sequential
specification legality nor the response extensions used in linearizability are defined here.

## References

* M. P. Herlihy and J. M. Wing, [*Linearizability: a correctness condition for concurrent
  objects*](https://www.cs.columbia.edu/~wing/publications/HerlihyWing90.pdf), ACM Transactions
  on Programming Languages and Systems 12(3) (1990), 463–492, §2.
-/

@[expose] public section

namespace Cslib.Distributed.ConcurrentHistories

/-- An invocation carries an operation name and a list of arguments. A response carries a
termination condition and a list of results, but no operation name. Names, conditions, and
payload values are represented by natural numbers. -/
inductive EventKind where
  | invocation (operation : ℕ) (arguments : List ℕ)
  | response (termination : ℕ) (results : List ℕ)
  deriving DecidableEq

/-- An invocation or response event tagged with its process and object (natural-number names). -/
structure Event where
  process : ℕ
  object : ℕ
  kind : EventKind
  deriving DecidableEq

/-- A finite event history is a list of invocation and response events, each tagged with a
process and an object. The list order is the global event order. No well-formedness condition
is imposed by the type. -/
abbrev History := List Event

/-- An event is an invocation if its kind carries an operation and arguments rather than a
termination condition and results. -/
def Event.IsInvocation (e : Event) : Prop :=
  match e.kind with
  | .invocation .. => True
  | .response .. => False

/-- A response `r` matches an invocation `i` in their labels if their process and object names
agree. This condition alone does not say where the two events occur in a history. -/
def Event.Matches (i r : Event) : Prop :=
  i.IsInvocation ∧ ¬ r.IsInvocation ∧ i.process = r.process ∧ i.object = r.object

/-- The process subhistory of `H` at `p` retains, in their original order, just the events
whose process name is `p`. Positions are not part of the event labels. -/
def History.project (H : History) (p : ℕ) : History :=
  H.filter fun e => e.process == p

/-- The object subhistory of `H` at `o` retains, in their original order, just the events
whose object name is `o`. -/
def History.projectObject (H : History) (o : ℕ) : History :=
  H.filter fun e => e.object == o

/-- A sequential event history consists of zero or more adjacent invocation–response pairs,
matching in process and object within each pair, then optionally one invocation. There is no
restriction on the labels across successive pairs. -/
inductive Sequential : History → Prop where
  | nil : Sequential []
  | pending {e : Event} : e.IsInvocation → Sequential [e]
  | pair {i r : Event} {tail : History} :
      i.Matches r → Sequential tail → Sequential (i :: r :: tail)

/-- A finite event history `H` is well formed if the subhistory at every process is sequential:
it consists of matched adjacent pairs and at most one pending invocation, at the end of that
process's subhistory. -/
def History.WellFormed (H : History) : Prop :=
  ∀ p, Sequential (H.project p)

/-- Two finite event histories are equivalent if their process subhistories are equal as lists
of event labels for every process. Their global interleaving need not be the same. -/
def History.Equivalent (H K : History) : Prop :=
  ∀ p, H.project p = K.project p

/-- Positions `i` and `j` in a finite event history are paired if `i < j`, the event at `j`
is a response matching the invocation at `i` in process and object, and no event of that
process lies strictly between them. In a well-formed history this is the invocation and its
next matching response. -/
def History.MatchesAt (H : History) (i j : Fin H.length) : Prop :=
  i < j ∧ (H.get i).Matches (H.get j) ∧
    ∀ k : Fin H.length, i < k → k < j → (H.get k).process ≠ (H.get i).process

private theorem Sequential.match_of_split {H : History} (hs : Sequential H) {i r : Event}
    (hi : i.IsInvocation) (pre post : History) (heq : H = pre ++ i :: r :: post) : i.Matches r := by
  induction hs generalizing pre with
  | nil => cases pre <;> simp at heq
  | pending _ =>
    cases pre with
    | nil => simp at heq
    | cons e pre =>
      have hn := (List.cons.inj heq).2
      cases pre <;> simp at hn
  | @pair a b tail hab _ ih =>
    cases pre with
    | nil =>
      have ea := (List.cons.inj heq).1
      have eb := (List.cons.inj (List.cons.inj heq).2).1
      exact ea ▸ eb ▸ hab
    | cons e pre =>
      have ht := (List.cons.inj heq).2
      cases pre with
      | nil => exact (hab.2.1 ((List.cons.inj ht).1.symm ▸ hi)).elim
      | cons e' pre => exact ih pre (List.cons.inj ht).2

private theorem History.pair_of_nextProcess {H : History} (hwf : H.WellFormed)
    {i j : Fin H.length} (hi : (H.get i).IsInvocation) (hij : i < j)
    (hp : (H.get j).process = (H.get i).process)
    (hbetween : ∀ k : Fin H.length, i < k → k < j → (H.get k).process ≠ (H.get i).process) :
    H.MatchesAt i j := by
  let gap := (H.drop (i.val + 1)).take (j.val - (i.val + 1))
  let keep : Event → Bool := fun e ↦ e.process == (H.get i).process
  have hgap : gap.filter keep = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he hkept
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp he
    have hn' := Nat.lt_of_lt_of_le hn (List.length_take_le (j.val - (i.val + 1)) _)
    have hik : i.val < i.val + 1 + n := by omega
    have hkj : i.val + 1 + n < j.val := by omega
    let k : Fin H.length := ⟨_, Nat.lt_trans hkj j.isLt⟩
    apply hbetween k hik hkj
    simpa only [keep, gap, k, List.getElem_take, List.getElem_drop, List.get_eq_getElem,
      beq_iff_eq] using hkept
  have hsuffix := List.take_append_drop (j.val - (i.val + 1)) (H.drop (i.val + 1))
  rw [List.drop_drop, show i.val + 1 + (j.val - (i.val + 1)) = j.val by omega,
    List.drop_eq_getElem_cons j.isLt] at hsuffix
  have hprefix := (List.take_append_drop i.val H).symm
  rw [List.drop_eq_getElem_cons i.isLt] at hprefix
  have hsplit : H = H.take i.val ++ H.get i :: (gap ++ H.get j :: H.drop (j.val + 1)) :=
    hprefix.trans (congrArg (fun suffix ↦ H.take i.val ++ H.get i :: suffix) hsuffix.symm)
  have hseq := hwf (H.get i).process
  change Sequential (H.filter keep) at hseq
  have hkeepi : keep (H.get i) := beq_self_eq_true _
  have hkeepj : keep (H.get j) := beq_iff_eq.mpr hp
  rw [hsplit] at hseq
  simp only [List.filter_append, List.filter_cons_of_pos hkeepi, List.filter_cons_of_pos hkeepj,
    hgap, List.nil_append] at hseq
  exact ⟨hij, hseq.match_of_split hi _ _ rfl, hbetween⟩

-- Take the least later position of this process. Sequentiality makes it a matching response.
private theorem History.exists_pair_le {H : History} (hwf : H.WellFormed) {i j : Fin H.length}
    (hi : (H.get i).IsInvocation) (hij : i < j) (hp : (H.get j).process = (H.get i).process) :
    ∃ k : Fin H.length, H.MatchesAt i k ∧ k.val ≤ j.val := by
  classical
  let P (n : ℕ) := ∃ hn : n < H.length,
    i.val < n ∧ (H.get ⟨n, hn⟩).process = (H.get i).process
  have hex : ∃ n, P n := ⟨j.val, j.isLt, hij, hp⟩
  obtain ⟨hk, hik, hkp⟩ := Nat.find_spec hex
  let k : Fin H.length := ⟨Nat.find hex, hk⟩
  refine ⟨k, H.pair_of_nextProcess hwf hi hik hkp ?_, Nat.find_min' hex ⟨j.isLt, hij, hp⟩⟩
  intro m him hmk hmp
  exact Nat.find_min hex hmk ⟨m.isLt, him, hmp⟩

/-- In a well-formed finite event history, positions `i` and `j` are paired if and only if
`j` is later than `i`, its event matches `i`'s invocation in process and object, and no response
matching that invocation occurs strictly between those positions. -/
theorem History.matchesAt_iff_next_matching {H : History} (hwf : H.WellFormed)
    (i j : Fin H.length) : H.MatchesAt i j ↔
      i < j ∧ (H.get i).Matches (H.get j) ∧
        ∀ k : Fin H.length, i < k → k < j → ¬ (H.get i).Matches (H.get k) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, fun k hik hkj hm ↦ h.2.2 k hik hkj hm.2.2.1.symm⟩
  · rintro ⟨hij, hm, hnext⟩
    obtain ⟨k, hk, hkj⟩ := History.exists_pair_le hwf hm.1 hij hm.2.2.1.symm
    rcases Nat.lt_or_eq_of_le hkj with hlt | heq
    · exact (hnext k hk.1 hlt hk.2.1).elim
    · rwa [← Fin.ext heq]

/-- An occurrence is pending if it is an invocation and has no following response paired to
it: no next event of its process is a matching response. In a well-formed history this is
exactly a process's final invocation with no matching response. -/
def History.Pending (H : History) (i : Fin H.length) : Prop :=
  (H.get i).IsInvocation ∧ ¬ ∃ j, H.MatchesAt i j

/-- A position of a well-formed finite event history is pending if and only if it holds an
invocation and no later event belongs to its process. In particular a pending invocation
need not be the last event of the whole history. -/
theorem History.pending_iff_last_for_process {H : History} (hwf : H.WellFormed)
    (i : Fin H.length) : H.Pending i ↔
      (H.get i).IsInvocation ∧ ∀ j : Fin H.length, i < j →
        (H.get j).process ≠ (H.get i).process := by
  constructor
  · rintro ⟨hi, hnone⟩
    refine ⟨hi, fun j hij hp => ?_⟩
    obtain ⟨k, hk, _⟩ := History.exists_pair_le hwf hi hij hp
    exact hnone ⟨k, hk⟩
  · rintro ⟨hi, hlast⟩
    exact ⟨hi, fun ⟨j, hj⟩ ↦ hlast j hj.1 hj.2.1.2.2.1.symm⟩

open Classical in
/-- Delete all pending invocation occurrences from `H`, retaining the other events in their
original order. For a well-formed history this leaves only invocations and their matching
responses; on a malformed list the definition still retains every response. -/
noncomputable def History.complete (H : History) : History :=
  (List.finRange H.length).filterMap fun i => if H.Pending i then none else some (H.get i)

/-- A completed operation of `H` is a pair of actual positions in `H`: an invocation and a
later response with the same process and object, with no intervening event of that process.
For well-formed `H` this gives the invocation and its next matching response. -/
structure CompletedOp (H : History) where
  /-- The invocation's zero-based position in `H`. -/
  invocation : Fin H.length
  /-- The response's zero-based position in `H`. -/
  response : Fin H.length
  /-- The invocation and response form a pair at those positions. -/
  paired : H.MatchesAt invocation response

/-- For two completed operations of the same history, the first precedes the second in strict
real time if the first response position is less than the second invocation position. -/
def RealTime {H : History} (a b : CompletedOp H) : Prop :=
  a.response < b.invocation

/-- No completed operation precedes itself in strict real time in any finite event history:
its invocation position is strictly less than its response position. -/
theorem realTime_irrefl {H : History} (a : CompletedOp H) : ¬ RealTime a a := by
  exact Fin.lt_asymm a.paired.1

/-- For three completed operations of the same finite event history, if the first precedes the
second and the second precedes the third in strict real time, then the first precedes the third. -/
theorem realTime_trans {H : History} {a b c : CompletedOp H}
    (hab : RealTime a b) (hbc : RealTime b c) : RealTime a c := by
  unfold RealTime at *
  exact Fin.lt_trans (Fin.lt_trans hab b.paired.1) hbc

/-- Export a completed operation of `H` to the completed-only `OpRec` model. The object,
operation name, and the original zero-based invocation and response positions are unchanged.
Two supplied functions encode the argument list and the termination condition with its result
list as natural numbers. The record does not retain the process; no injectivity of the payload
encodings is assumed. -/
def CompletedOp.toOpRec {H : History} (a : CompletedOp H) (encodeArgs : List ℕ → ℕ)
    (encodeResult : ℕ → List ℕ → ℕ) : Linearizability.OpRec :=
  let i := H.get a.invocation
  let r := H.get a.response
  let call := match h : i.kind with
    | .invocation op args => (op, args)
    | .response .. => False.elim (by
      simpa only [Event.IsInvocation, h] using (show i.IsInvocation from a.paired.2.1.1))
  let reply := match h : r.kind with
    | .response term results => (term, results)
    | .invocation .. => False.elim (a.paired.2.1.2.1 (show r.IsInvocation by
        simp only [Event.IsInvocation, h]))
  ⟨i.object, call.1, encodeArgs call.2, encodeResult reply.1 reply.2,
    a.invocation, a.response, a.paired.1⟩

private theorem CompletedOp.eq_of_positions {H : History} {a b : CompletedOp H}
    (hi : a.invocation = b.invocation) (hr : a.response = b.response) : a = b := by
  cases a
  cases b
  cases hi
  cases hr
  rfl

private theorem History.response_unique {H : History} {i j k : Fin H.length}
    (hij : H.MatchesAt i j) (hik : H.MatchesAt i k) : j = k := by
  rcases Nat.lt_trichotomy j.val k.val with h | h | h
  · exact (hik.2.2 j hij.1 h hij.2.1.2.2.1.symm).elim
  · exact Fin.ext h
  · exact (hij.2.2 k hik.1 h hik.2.1.2.2.1.symm).elim

private theorem History.invocation_unique {H : History} {i j k : Fin H.length}
    (hik : H.MatchesAt i k) (hjk : H.MatchesAt j k) : i = j := by
  have hproc := hik.2.1.2.2.1.trans hjk.2.1.2.2.1.symm
  rcases Nat.lt_trichotomy i.val j.val with h | h | h
  · exact (hik.2.2 j h hjk.1 hproc.symm).elim
  · exact Fin.ext h
  · exact (hjk.2.2 i h hik.1 hproc).elim

/-- Exporting a list of distinct completed operations from a single finite event history gives
an `OpRec` history with pairwise distinct event positions (`Linearizability.WellFormed`). This
holds for any payload encodings; pairing at consecutive occurrences of a process ensures that
no invocation or response position can be shared by two distinct operations. It does not
require the rest of the event history to be well formed. -/
theorem wellFormed_map_toOpRec {H : History} {ops : List (CompletedOp H)} (h : ops.Nodup)
    (encodeArgs : List ℕ → ℕ) (encodeResult : ℕ → List ℕ → ℕ) :
    Linearizability.WellFormed (ops.map fun a => a.toOpRec encodeArgs encodeResult) := by
  unfold Linearizability.WellFormed Linearizability.eventPositions
  rw [List.flatMap_map]
  change (ops.flatMap fun a => [a.invocation.val, a.response.val]).Nodup
  rw [List.Nodup, List.pairwise_flatMap]
  refine ⟨fun a _ => ?_, h.imp ?_⟩
  · exact .cons (by simpa using Nat.ne_of_lt a.paired.1) (.cons (by simp) .nil)
  · intro a b hab i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · intro heq
      have heq' : a.invocation = b.invocation := Fin.ext heq
      apply hab (CompletedOp.eq_of_positions heq' (History.response_unique a.paired ?_))
      simpa only [heq'] using b.paired
    · intro heq
      have heq' : a.invocation = b.response := Fin.ext heq
      exact b.paired.2.1.2.1 (heq' ▸ a.paired.2.1.1)
    · intro heq
      have heq' : a.response = b.invocation := Fin.ext heq
      exact a.paired.2.1.2.1 (heq'.symm ▸ b.paired.2.1.1)
    · intro heq
      have heq' : a.response = b.response := Fin.ext heq
      apply hab (CompletedOp.eq_of_positions (History.invocation_unique a.paired ?_) heq')
      simpa only [heq'] using b.paired

/-- A list of completed operations of one finite history respects the history's real-time
order (no later entry precedes an earlier one) if and only if its list of `OpRec` exports
satisfies `RespectsRT`. The supplied payload encodings are arbitrary, and the equivalence
does not require distinct list entries. -/
theorem respectsRT_map_toOpRec_iff {H : History} (ops : List (CompletedOp H))
    (encodeArgs : List ℕ → ℕ) (encodeResult : ℕ → List ℕ → ℕ) :
    Linearizability.RespectsRT (ops.map fun a => a.toOpRec encodeArgs encodeResult) ↔
      ops.Pairwise (fun a b => ¬ RealTime b a) := by
  rw [Linearizability.RespectsRT, List.pairwise_map]
  rfl

end Cslib.Distributed.ConcurrentHistories
