/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.ConcurrentHistories

/-!
# Tests for finite concurrent histories

Two processes invoke overlapping operations on the same object. The first process then
invokes on a different object and leaves the call pending, even though the other process
still has events. The examples check process equivalence, completion, matching by object
and process, and the real-time order in the event model and in the completed-only export.
-/

namespace Cslib.Distributed.ConcurrentHistories.Tests

private def aCall : Event := ⟨0, 7, .invocation 3 [8, 9]⟩
private def aReply : Event := ⟨0, 7, .response 4 [10]⟩
private def bCall : Event := ⟨1, 7, .invocation 3 [11]⟩
private def bReply : Event := ⟨1, 7, .response 0 [12]⟩
private def pendingCall : Event := ⟨0, 8, .invocation 5 []⟩

-- The two occurrences of B's call and reply have the same labels but distinct positions.
private abbrev hist : History := [aCall, bCall, bReply, aReply, pendingCall, bCall, bReply]

private theorem aMatches : aCall.Matches aReply := ⟨trivial, id, rfl, rfl⟩
private theorem bMatches : bCall.Matches bReply := ⟨trivial, id, rfl, rfl⟩

example : hist.project 0 = [aCall, aReply, pendingCall] := rfl
example : hist.project 1 = [bCall, bReply, bCall, bReply] := rfl

example : hist.WellFormed := by
  intro p
  by_cases h0 : p = 0
  · subst p
    exact .pair aMatches (.pending trivial)
  by_cases h1 : p = 1
  · subst p
    exact .pair bMatches (.pair bMatches .nil)
  simpa [History.project, hist, aCall, aReply, bCall, bReply, pendingCall,
    Ne.symm h0, Ne.symm h1] using Sequential.nil

-- Object projection need not be sequential, even for a well-formed history.
example : ¬ Sequential (hist.projectObject 7) := by
  change ¬ Sequential [aCall, bCall, bReply, aReply, bCall, bReply]
  intro h
  cases h with
  | pair hm _ => exact hm.2.1 trivial

-- Changing the interleaving preserves these process subhistories, including the pending call.
example : hist.Equivalent [bCall, bReply, aCall, aReply, pendingCall, bCall, bReply] := by
  intro p
  by_cases h0 : p = 0
  · subst p
    rfl
  by_cases h1 : p = 1
  · subst p
    rfl
  simp [History.project, hist, aCall, aReply, bCall, bReply, pendingCall, Ne.symm h0, Ne.symm h1]

example : ¬ hist.Equivalent [aCall, bCall, bReply, aReply, bCall, bReply] :=
  fun h => by have := h 0; contradiction

-- Same process, wrong object, despite a response immediately following the invocation.
private def wrongObject : History := [aCall, ⟨0, 8, .response 4 [10]⟩]

example : ¬ wrongObject.WellFormed := by
  intro h
  have h0 : Sequential wrongObject := h 0
  cases h0 with
  | pair hm _ => exact (by decide : (7 : ℕ) ≠ 8) hm.2.2.2

-- Same object, wrong process.
example : ¬ aCall.Matches bReply := fun h => (by decide : (0 : ℕ) ≠ 1) h.2.2.1

private def a : CompletedOp hist := ⟨0, 3, by
  refine ⟨by decide, aMatches, ?_⟩
  intro k hk₀ hk₃
  change 0 < k.val at hk₀
  change k.val < 3 at hk₃
  have hk : k.val = 1 ∨ k.val = 2 := by omega
  rcases hk with hk | hk
  · have h : k = 1 := Fin.ext hk
    subst k
    decide
  · have h : k = 2 := Fin.ext hk
    subst k
    decide⟩

private def b : CompletedOp hist := ⟨1, 2, ⟨by decide, bMatches, by
  intro k hk₁ hk₂
  change 1 < k.val at hk₁
  change k.val < 2 at hk₂
  omega⟩⟩

private def b' : CompletedOp hist := ⟨5, 6, ⟨by decide, bMatches, by
  intro k hk₅ hk₆
  change 5 < k.val at hk₅
  change k.val < 6 at hk₆
  omega⟩⟩

-- The identical later reply cannot be paired with the first B invocation.
example : ¬ hist.MatchesAt 1 6 := fun h => h.2.2 2 (by decide) (by decide) rfl

private theorem pending_four : hist.Pending 4 := by
  refine ⟨trivial, ?_⟩
  rintro ⟨j, hj⟩
  have hj' : j.val = 5 ∨ j.val = 6 := by
    have hlt : 4 < j.val := hj.1
    have hbound : j.val < 7 := j.isLt
    omega
  rcases hj' with hj' | hj'
  · have h : j = 5 := Fin.ext hj'
    subst j
    exact hj.2.1.2.1 trivial
  · have h : j = 6 := Fin.ext hj'
    subst j
    exact (by decide : (0 : ℕ) ≠ 1) hj.2.1.2.2.1

-- Deletion preserves the exact order and the two repeated B invocations and responses.
example : hist.complete = [aCall, bCall, bReply, aReply, bCall, bReply] := by
  classical
  have noPending {i j : Fin hist.length} (h : hist.MatchesAt i j) : ¬ hist.Pending i :=
    fun hp => hp.2 ⟨j, h⟩
  have noPending0 : ¬ hist.Pending 0 := noPending a.paired
  have noPending1 : ¬ hist.Pending 1 := noPending b.paired
  have noPending5 : ¬ hist.Pending 5 := noPending b'.paired
  have notPendingReply (i : Fin hist.length) (hi : ¬ (hist.get i).IsInvocation) :
      ¬ hist.Pending i := fun hp => hi hp.1
  change (List.finRange 7).filterMap (fun (i : Fin hist.length) ↦
    if hist.Pending i then none else some (hist.get i)) = _
  rw [show List.finRange 7 = [0, 1, 2, 3, 4, 5, 6] by decide]
  simp only [List.filterMap_cons, List.filterMap_nil, noPending0, noPending1, noPending5,
    notPendingReply 2 id, notPendingReply 3 id, notPendingReply 6 id, pending_four,
    ite_true, ite_false]
  rfl

-- A and B overlap, but both complete before the later B invocation.
example : ¬ RealTime a b ∧ ¬ RealTime b a := by unfold RealTime; decide
example : RealTime a b' ∧ RealTime b b' ∧ ¬ RealTime b' a := by unfold RealTime; decide

private def record (op : CompletedOp hist) : Linearizability.OpRec :=
  op.toOpRec List.sum (fun term results ↦ term + results.sum)

example : record a = ⟨7, 3, 17, 14, 0, 3, by decide⟩ := rfl
example : record b' = ⟨7, 3, 11, 12, 5, 6, by decide⟩ := rfl

-- The original event positions are distinct, even for repeated labels.
example : Linearizability.WellFormed ([a, b, b'].map record) := by
  unfold Linearizability.WellFormed Linearizability.eventPositions
  decide

example : Linearizability.RespectsRT ([b, a, b'].map record) := by
  change Linearizability.RespectsRT ([b, a, b'].map (fun op ↦
    op.toOpRec List.sum (fun term results ↦ term + results.sum)))
  rw [respectsRT_map_toOpRec_iff]
  unfold RealTime
  decide

example : ¬ Linearizability.RespectsRT ([b', a, b].map record) := fun h => by
  have ht := (Linearizability.respectsRT_iff _).1 h 1 0 (by decide) (by decide) (by decide)
  omega

end Cslib.Distributed.ConcurrentHistories.Tests
