/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight
import CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight.Hardness
import CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight.Membership
meta import CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight.Membership
meta import MathlibExt.Computability.Complexity

/-! # Tests for the NP-completeness of CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT -/

namespace MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

-- The original statement, with its exact type.
example :
    constrainedSequencingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L constrainedSequencingDec :=
  constrainedSequencing_npComplete

example : constrainedSequencingDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  constrainedSequencing_mem_NP

example (L : MetaMathlibExt.ComplexityTheory.DecisionProblem)
    (hL : L ∈ MetaMathlibExt.ComplexityTheory.NP) :
    Cslib.CookLevin.PolyManyOneRed L constrainedSequencingDec :=
  constrainedSequencing_npHard L hL

example (x : List Bool) : constrainedSequencingDec x = true ↔
    ∃ w : List Bool, w.length ≤ x.length ^ 2 ∧ Verification.check x w = true :=
  Verification.check_iff x

private theorem accepts_encoding (i : ConstrainedSequencingInstance) :
    constrainedSequencingDec (bitEncode i) = true ↔
      WellFormed i ∧ ConstrainedSequencingFeasible i := by
  simp [constrainedSequencingDec, bitDecode_bitEncode]

/-- Two unit-length tasks with deadline `1`, of weights `5` and `7`, the bound `K = 5`, and
`S = {1}`, `J = 1`. -/
private def yesInstance : ConstrainedSequencingInstance := (([(1, 1, 5), (1, 1, 7)], 5), [1], 1)

/-- The same tasks with `K = 6`, `S = {0}` and `J = 1`. -/
private def noInstance : ConstrainedSequencingInstance := (([(1, 1, 5), (1, 1, 7)], 6), [0], 1)

/-- Running task `1` first meets its deadline, and task `0`, of weight `5`, is the only tardy
task. -/
example : constrainedSequencingDec (bitEncode yesInstance) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold yesInstance WellFormed; decide, [1, 0], by decide, by decide, by decide⟩

/-- Task `0` meets its deadline only when it runs first, and then task `1`, of weight `7 > 6`,
is tardy; the bound `K = 6` alone allows running task `1` first. -/
example : constrainedSequencingDec (bitEncode noInstance) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, order, hp, hw, hs⟩ := ((accepts_encoding _).1 h)
  have hlen : order.length = 2 := by simpa [noInstance] using hp.length_eq
  rcases order with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp at hlen
  have ha : a ∈ List.range 2 := hp.subset (by simp)
  have hb : b ∈ List.range 2 := hp.subset (by simp)
  have hab : [a, b].Nodup := hp.nodup_iff.2 List.nodup_range
  simp only [List.mem_range, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at ha hb hab
  rcases (by omega : a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    revert hw hs <;> decide

/-- The unconstrained bound is met: running task `1` first leaves only task `0` tardy. -/
example : WeightedTardyJobs.WeightedTardy [(1, 1, 5), (1, 1, 7)] [1, 0] ≤ 6 := by decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : constrainedSequencingDec [true] = false := by
  have h : bitDecode (α := ConstrainedSequencingInstance) [true] = none := rfl
  simp [constrainedSequencingDec, h]

-- The verifier accepts the plan that sets task `0` aside, selects task `1`, then selects task `0`.
#guard Verification.check (bitEncode yesInstance) [true, false, false]
-- Running the tasks in index order leaves task `1`, of weight `7 > 5`, tardy.
#guard !Verification.check (bitEncode yesInstance) [false, false]
-- A plan must select every task.
#guard !Verification.check (bitEncode yesInstance) [true, false]
-- On the no-instance both orders are rejected.
#guard !Verification.check (bitEncode noInstance) [false, false]
#guard !Verification.check (bitEncode noInstance) [true, false, false]
-- The bound `K = 0` is malformed, and the verifier rejects it before reading the plan.
#guard !Verification.check (bitEncode ((([(1, 1, 5), (1, 1, 7)], 0), [1], 1) :
  ConstrainedSequencingInstance)) [true, false, false]
-- An element of `S` that is not a task index is rejected.
#guard !Verification.check (bitEncode ((([(1, 1, 5), (1, 1, 7)], 5), [2], 1) :
  ConstrainedSequencingInstance)) [true, false, false]
-- An undecodable instance is rejected.
#guard !Verification.check [true] []

end MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight
