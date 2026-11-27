/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.OnlineConvexLowerBound
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tests for the online convex optimization lower bound
-/

namespace CSLibExtTest.MachineLearning.OnlineConvexLowerBound

open Cslib.MachineLearning.OnlineConvexLowerBound

/-- T1: at `T = 1` the total absolute sign sum over both sequences is `2`. -/
example : ∑ σ : Fin 1 → Bool, |∑ t : Fin 1, BooleanCube.cubeVal (σ t)| = 2 := by
  have hcube : ∀ b : Bool, |BooleanCube.cubeVal b| = 1 := by
    intro b
    cases b <;> simp [BooleanCube.cubeVal]
  simp only [Fin.sum_univ_one, hcube, Finset.sum_const, Finset.card_univ,
    show Fintype.card (Fin 1 → Bool) = 2 from by decide]
  simp

/-- At `T = 2` the squared sign-sum over all four sequences is `8`,
by direct evaluation of the four cases. -/
example : ∑ σ : Fin 2 → Bool, (∑ t : Fin 2, BooleanCube.cubeVal (σ t)) ^ 2 = 8 := by
  have h := Equiv.sum_comp (finTwoArrowEquiv Bool).symm
    (fun σ : Fin 2 → Bool => (∑ t : Fin 2, BooleanCube.cubeVal (σ t)) ^ 2)
  rw [← h, Fintype.sum_prod_type]
  simp only [finTwoArrowEquiv_symm_apply, Fin.sum_univ_two,
    Fintype.sum_bool]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [BooleanCube.cubeVal]
  ring

/-- T2: the always-zero algorithm at `T = 2`, `D = 2`, `G = 1` suffers
regret `2` against the all-`true` sign sequence. -/
theorem t2_regret_value :
    regret 2 (fun _ _ => 0) 2 1 (fun _ => true) = 2 := by
  have hplay : ∀ t : Fin 2, playAt 2 (fun _ _ => 0) (fun _ => true) t
      = 0 := fun t => rfl
  have hcube : BooleanCube.cubeVal true = 1 := rfl
  show (∑ t : Fin 2,
      BooleanCube.cubeVal ((fun _ => true) t) * 1 * playAt 2 (fun _ _ => 0) (fun _ => true) t)
      + 1 * (2 / 2) * |∑ t : Fin 2, BooleanCube.cubeVal ((fun _ => true) t)| = 2
  simp only [hplay, mul_zero, Finset.sum_const_zero, zero_add, hcube,
    Fin.sum_univ_two]
  rw [one_add_one_eq_two, abs_of_nonneg zero_le_two,
    div_self (by linarith : (2 : ℝ) ≠ 0)]
  ring

/-- T2: that regret beats the hand-computed numeric bound
`(2 * 1 / 2) * Real.sqrt (2 / 3)` at this instance. -/
example : (2 * 1 / 2 : ℝ) * Real.sqrt ((2 : ℝ) / 3)
    ≤ regret 2 (fun _ _ => 0) 2 1 (fun _ => true) := by
  rw [t2_regret_value]
  have hcoef : (2 * 1 / 2 : ℝ) = 1 := by ring
  rw [hcoef, one_mul]
  have hle : (Real.sqrt ((2 : ℝ) / 3)) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    rw [Real.sq_sqrt (div_nonneg zero_le_two zero_le_three),
      show (2 : ℝ) ^ 2 = 4 from by ring, div_le_iff₀ three_pos]
    linarith
  exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) zero_le_two hle

/-- T3: `-10` is the least value of `5 * x` over `|x| ≤ 2`. -/
theorem comparator_min_isLeast :
    IsLeast {y : ℝ | ∃ x : ℝ, |x| ≤ 2 ∧ 5 * x = y} (-10) := by
  constructor
  · obtain ⟨x, hx_le, hx_eq⟩ :=
      comparator_attained 4 1 5 (by linarith) (by linarith)
    have h42 : (4 : ℝ) / 2 = 2 := by linarith
    have habs5 : |(5 : ℝ)| = 5 := abs_of_nonneg (by linarith)
    rw [h42] at hx_le
    rw [h42, habs5] at hx_eq
    have hx_eq' : 5 * x = -10 := by linarith
    exact ⟨x, hx_le, hx_eq'⟩
  · rw [mem_lowerBounds]
    intro y hy
    obtain ⟨x, hx_le, hx_eq⟩ := hy
    have h42 : (4 : ℝ) / 2 = 2 := by linarith
    have hx_le' : |x| ≤ 4 / 2 := by rw [h42]; exact hx_le
    have hlb :=
      comparator_lower_bound 4 1 5 x (by linarith) (by linarith) hx_le'
    have habs5 : |(5 : ℝ)| = 5 := abs_of_nonneg (by linarith)
    rw [h42, habs5] at hlb
    have hlb' : (-10 : ℝ) ≤ 5 * x := by linarith
    rw [← hx_eq]
    exact hlb'

/-- Adaptivity: `playAt` at round zero ignores the current sign. -/
example (A : ∀ t : ℕ, (Fin t → Bool) → ℝ) :
    playAt 1 A (fun _ => true) 0
      = playAt 1 A (fun _ => false) 0 := by
  unfold playAt
  congr 1
  funext i
  exact Fin.elim0 i

/-- A non-zero test algorithm used for the expectation check below. -/
def testAlg : ∀ t : ℕ, (Fin t → Bool) → ℝ := fun t _ => (t : ℝ) + 1

/-- `online_play_expectation_zero` at `T = 1` for `testAlg`. -/
example : ∑ σ : Fin 1 → Bool, BooleanCube.cubeVal (σ 0) * playAt 1 testAlg σ 0 = 0 :=
  online_play_expectation_zero 1 testAlg 0

/-- `oco_lower_bound` at `T = 1`, `D = 2`, `G = 1` for the zero algorithm. -/
example : ∃ σ : Fin 1 → Bool,
    (2 * 1 / 2 : ℝ) * Real.sqrt (((1 : ℕ) : ℝ) / 3)
      ≤ regret 1 (fun _ _ => 0) 2 1 σ :=
  oco_lower_bound 1 (fun _ _ => 0) 2 1 (by decide) (by linarith)
    (by linarith) (by intro t s; simp)

-- Guarded axiom audit for the lower-bound theorems.
/--
info: 'Cslib.MachineLearning.OnlineConvexLowerBound.online_play_expectation_zero' depends on
 axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms online_play_expectation_zero
/--
info: 'Cslib.MachineLearning.OnlineConvexLowerBound.oco_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms oco_lower_bound

end CSLibExtTest.MachineLearning.OnlineConvexLowerBound
