/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardiness

/-- The length of the only task in a one-task instance. -/
example : taskLength ([(2, 3, 4)], 5) ⟨0, by decide⟩ = 2 := rfl

/-- The weight and deadline of the second task in a two-task instance. -/
example :
    weight ([(2, 3, 4), (1, 7, 9)], 5) ⟨1, by decide⟩ = 7 ∧
      deadline ([(2, 3, 4), (1, 7, 9)], 5) ⟨1, by decide⟩ = 9 :=
  ⟨rfl, rfl⟩

/-- A well-formed instance: every length, weight and deadline is positive, and so is `K`. -/
example : WellFormed ([(2, 3, 4), (1, 7, 9)], 5) := by
  simp [WellFormed]

/-- A malformed instance: one task has length zero. -/
example : ¬ WellFormed ([(0, 1, 1)], 1) := by
  simp [WellFormed]

/-- A malformed instance: the bound `K` is zero. -/
example : ¬ WellFormed ([(1, 1, 1)], 0) := by
  simp [WellFormed]

/-- Starting the second task when the first one ends is a one-processor schedule. -/
example : IsOneProcessorSchedule ![2, 1] ![0, 2] := by
  unfold IsOneProcessorSchedule Function.Injective
  decide

/-- Overlapping tasks do not form a one-processor schedule. -/
example : ¬ IsOneProcessorSchedule ![2, 1] ![0, 1] := by
  unfold IsOneProcessorSchedule Function.Injective
  decide

/-- Two tasks starting at the same time do not form a one-processor schedule. -/
example : ¬ IsOneProcessorSchedule ![1, 1] ![0, 0] := by
  unfold IsOneProcessorSchedule Function.Injective
  decide

/-- A schedule meeting both deadlines has weighted tardiness `0`. -/
example : SequencingToMinimizeWeightedTardinessFeasible ([(2, 3, 4), (1, 7, 9)], 5) :=
  ⟨![0, 2], by unfold IsOneProcessorSchedule Function.Injective; decide, by decide⟩

/-- A task of length `3`, weight `2` and deadline `1` started at time `0` is late by `2`, so
its weighted tardiness is `4`, which the bound `4` admits. -/
example : SequencingToMinimizeWeightedTardinessFeasible ([(3, 2, 1)], 4) :=
  ⟨![0], by unfold IsOneProcessorSchedule Function.Injective; decide, by decide⟩

/-- The same task has weighted tardiness at least `4` under every schedule, so the bound `3`
admits none. -/
example : ¬ SequencingToMinimizeWeightedTardinessFeasible ([(3, 2, 1)], 3) := by
  rintro ⟨σ, -, h⟩
  have hmem : (⟨0, by decide⟩ : Task ([(3, 2, 1)], 3)) ∈ Finset.univ.filter
      (fun t => deadline ([(3, 2, 1)], 3) t < σ t + taskLength ([(3, 2, 1)], 3) t) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show 1 < _ + 3
    omega
  have h4 : (σ ⟨0, by decide⟩ + 3 - 1) * 2 ≤ 3 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem).trans h
  omega

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardiness
