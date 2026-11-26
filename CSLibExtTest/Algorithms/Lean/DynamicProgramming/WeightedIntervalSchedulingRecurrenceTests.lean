/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.WeightedIntervalScheduling
public import CSLibExt.Algorithms.Lean.DynamicProgramming.WeightedIntervalSchedulingRecurrence
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.WeightedIntervalScheduling
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.WeightedIntervalSchedulingRecurrence
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
meta import Mathlib.Algebra.Order.Group.Int

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.WeightedIntervalSchedulingRecurrenceTests

open Cslib.Algorithms.Lean.WeightedIntervalScheduling
open Cslib.Algorithms.Lean.TimeM (IntervalCompatible intervalCompatible_iff_disjoint_Ico)

/-! ### A sorted instance

Intervals `[0, 3)`, `[1, 5)`, `[4, 6)`, `[3, 8)`, `[6, 9)` with weights `2, 4, 4, 7, 2`, already in
finish order. Then `p = (0, 0, 1, 1, 3)` and `OPT = (0, 2, 4, 6, 9, 9)`; the traceback takes the
touching intervals `[0, 3)` and `[3, 8)`. -/

/-- Start times of the sorted instance. -/
def s₁ (i : ℕ) : ℕ := [0, 1, 4, 3, 6].getD (i - 1) 0

/-- Finish times of the sorted instance. -/
def f₁ (i : ℕ) : ℕ := [3, 5, 6, 8, 9].getD (i - 1) 0

/-- Weights of the sorted instance. -/
def w₁ (i : ℕ) : ℕ := [2, 4, 4, 7, 2].getD (i - 1) 0

#guard (List.range' 1 5).map (wisPred s₁ f₁) = [0, 0, 1, 1, 3]
#guard (List.range 6).map (wisValue s₁ f₁ w₁) = [0, 2, 4, 6, 9, 9]
#guard wisTrace s₁ f₁ w₁ 5 = {1, 4}
#guard wisTrace s₁ f₁ w₁ 3 = {1, 3}
#guard wisTrace s₁ f₁ w₁ 0 = ∅

-- The recurrence agrees with the brute-force optimum `wisOpt` on every prefix.
#guard (List.range 6).all fun j => wisValue s₁ f₁ w₁ j = wisOpt s₁ f₁ w₁ (Finset.Icc 1 j)

-- The bottom-up table and the binary searches reproduce `OPT` and `p`.
#guard (wisTable s₁ f₁ w₁ 5).ret = (#[0, 2, 4, 6, 9, 9], #[0, 0, 0, 1, 1, 3])

/-! ### The same intervals out of finish order -/

/-- Start times of the permuted instance: `[3, 8)`, `[1, 5)`, `[6, 9)`, `[0, 3)`, `[4, 6)`. -/
def s₂ (i : ℕ) : ℕ := [3, 1, 6, 0, 4].getD (i - 1) 0

/-- Finish times of the permuted instance. -/
def f₂ (i : ℕ) : ℕ := [8, 5, 9, 3, 6].getD (i - 1) 0

/-- Weights of the permuted instance. -/
def w₂ (i : ℕ) : ℕ := [7, 4, 2, 2, 4].getD (i - 1) 0

#guard (wisSchedule s₂ f₂ w₂ 5).ret = (9, {1, 4})
#guard (wisSchedule s₂ f₂ w₂ 5).ret.1 = wisOpt s₂ f₂ w₂ (Finset.Icc 1 5)
#guard (wisSchedule s₂ f₂ w₂ 5).time ≤ 2 * 5 * Nat.clog 2 5 + 2 * 5

/-! ### Boundary cases -/

-- No intervals: value `0`, the empty schedule and no comparisons.
#guard (wisSchedule s₂ f₂ w₂ 0).ret = (0, ∅)
#guard (wisSchedule s₂ f₂ w₂ 0).time = 0

-- One interval: merge sort and the binary search make no comparison; the table and the
-- traceback make one each.
#guard (wisSchedule s₂ f₂ w₂ 1).ret = (7, {1})
#guard (wisSchedule s₂ f₂ w₂ 1).time = 2

-- Equal finish times: intervals `[2, 4)`, `[1, 2)` and `[0, 2)` with weights `1`, `5` and `1`.
-- The last two overlap and both are compatible with the first, so the optimum is `{1, 2}`.
#guard (wisSchedule (fun i => [2, 1, 0].getD (i - 1) 0) (fun i => [4, 2, 2].getD (i - 1) 0)
  (fun i => ([1, 5, 1].getD (i - 1) 0 : ℕ)) 3).ret = (6, {1, 2})

-- Negative weights need no special treatment: an interval of negative weight is never taken.
#guard (wisSchedule (fun _ => (0 : ℕ)) (fun _ => 1) (fun _ => (-3 : ℤ)) 1).ret = (0, ∅)
#guard (wisSchedule (fun i => [0, 1].getD (i - 1) 0) (fun i => [1, 2].getD (i - 1) 0)
  (fun i => ([-3, 2].getD (i - 1) 0 : ℤ)) 2).ret = (2, {2})

-- Without positive lengths the recurrence can fail: `[1, 1)` followed by `[0, 1)`, both of weight
-- `1`, have sorted finish times and are compatible, so the optimum is `2`, but `OPT(2) = 1`.
#guard wisValue (fun i => [1, 0].getD (i - 1) 0) (fun _ => (1 : ℕ)) (fun _ => (1 : ℕ)) 2 = 1
#guard wisOpt (fun i => [1, 0].getD (i - 1) 0) (fun _ => (1 : ℕ)) (fun _ => (1 : ℕ))
  (Finset.Icc 1 2) = 2

/-! ### Binary search -/

-- The last index of `1, …, 4` with finish time at most `x`, or `0`, on finish times `3, 5, 6, 8`.
#guard (List.range 10).map (fun x => (predSearch f₁ x 0 4).ret) = [0, 0, 0, 1, 1, 2, 3, 3, 4, 4]
#guard (List.range 10).all fun x => (predSearch f₁ x 0 4).time ≤ Nat.clog 2 5

/-! ### Consequences of the main theorem -/

/-- For natural weights, the recurrence on sorted intervals of positive length is `wisOpt` on
every prefix. -/
example (start finish : ℕ → ℕ) (weight : ℕ → ℕ) (n : ℕ)
    (hpos : ∀ i ∈ Set.Icc 1 n, start i < finish i) (hmono : MonotoneOn finish (Set.Icc 1 n))
    (j : ℕ) (hj : j ≤ n) :
    wisValue start finish weight j = wisOpt start finish weight (Finset.Icc 1 j) :=
  ((isOptimalSchedule_wisTrace_and_wisSchedule start finish weight n hpos).1 hmono j hj).eq_wisOpt

/-- For natural weights, the algorithm returns `wisOpt` on unsorted intervals of positive
length. -/
example (start finish : ℕ → ℕ) (weight : ℕ → ℕ) (n : ℕ)
    (hpos : ∀ i ∈ Set.Icc 1 n, start i < finish i) :
    (wisSchedule start finish weight n).ret.1 = wisOpt start finish weight (Finset.Icc 1 n) :=
  (isOptimalSchedule_wisTrace_and_wisSchedule start finish weight n hpos).2.1.eq_wisOpt

/-- The algorithm's schedule has its returned value as its weight, for integer times and integer
weights of either sign. -/
example (start finish : ℕ → ℤ) (weight : ℕ → ℤ) (n : ℕ)
    (hpos : ∀ i ∈ Set.Icc 1 n, start i < finish i) :
    ∑ i ∈ (wisSchedule start finish weight n).ret.2, weight i =
      (wisSchedule start finish weight n).ret.1 :=
  (isOptimalSchedule_wisTrace_and_wisSchedule start finish weight n hpos).2.1.2.2.1

/-- Touching intervals `[0, 1)` and `[1, 2)` are compatible and disjoint. -/
example : Disjoint (Set.Ico (0 : ℕ) 1) (Set.Ico 1 2) :=
  (intervalCompatible_iff_disjoint_Ico (start := fun i : Fin 2 => (i : ℕ))
    (finish := fun i => (i : ℕ) + 1) (a := 0) (b := 1) (by simp) (by simp)).mp (Or.inl le_rfl)

/-- Overlapping intervals `[0, 2)` and `[1, 3)` are not compatible. -/
example : ¬IntervalCompatible (fun i : Fin 2 => (i : ℕ)) (fun i => (i : ℕ) + 2) 0 1 := by
  rw [intervalCompatible_iff_disjoint_Ico (by simp) (by simp), Set.Ico_disjoint_Ico]
  simp

/--
info: 'Cslib.Algorithms.Lean.WeightedIntervalScheduling.isOptimalSchedule_wisTrace_and_wisSchedule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isOptimalSchedule_wisTrace_and_wisSchedule

/--
info: 'Cslib.Algorithms.Lean.TimeM.intervalCompatible_iff_disjoint_Ico' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms intervalCompatible_iff_disjoint_Ico

/--
info: 'Cslib.Algorithms.Lean.WeightedIntervalScheduling.IsOptimalSchedule.eq_wisOpt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsOptimalSchedule.eq_wisOpt

end Cslib.Algorithms.Lean.WeightedIntervalSchedulingRecurrenceTests
