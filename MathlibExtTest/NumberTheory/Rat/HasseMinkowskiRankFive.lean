/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Rat.HasseMinkowskiRankFive

/-!
# Tests for the rank `n ≥ 5` step of the Hasse–Minkowski theorem over `ℚ`
-/

set_option autoImplicit false

namespace HasseMinkowskiRankFiveTest

open Rat Rat.Place

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The class of the positive reals is open. -/
example : IsOpen {y : ℝ | ∃ z : ℝ, z ≠ 0 ∧ y = 1 * z ^ 2} :=
  isOpen_squareClass .infinite (x := (1 : ℝ)) one_ne_zero

/-- The class of the negative reals is open. -/
example : IsOpen {y : ℝ | ∃ z : ℝ, z ≠ 0 ∧ y = -3 * z ^ 2} :=
  isOpen_squareClass .infinite (x := (-3 : ℝ)) (by norm_num)

/-- A `5`-adic square class is open. -/
example : IsOpen {y : ℚ_[5] | ∃ z : ℚ_[5], z ≠ 0 ∧ y = 2 * z ^ 2} :=
  isOpen_squareClass (.finite ⟨5, Fact.out⟩) (x := (2 : ℚ_[5])) two_ne_zero

/-- A `2`-adic square class is open. -/
example : IsOpen {y : ℚ_[2] | ∃ z : ℚ_[2], z ≠ 0 ∧ y = 3 * z ^ 2} :=
  isOpen_squareClass (.finite ⟨2, Nat.prime_two⟩) (x := (3 : ℚ_[2])) three_ne_zero

/-- The step applied to `x₁² - x₂² + 2 x₃² + 3 x₄² + 5 x₅²`, with the explicit local zero
`(1, 1, 0, 0, 0)` at every place and the ranks `3` and `4` as hypothesis. -/
example (ih : ∀ m : ℕ, (m = 5 - 2 ∨ m = 5 - 1) → ∀ b : Fin m → ℚ, (∀ i, b i ≠ 0) →
      (∃ x : Fin m → ℝ, x ≠ 0 ∧ ∑ i, (b i : ℝ) * x i ^ 2 = 0) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin m → ℚ_[p], x ≠ 0 ∧ ∑ i, (b i : ℚ_[p]) * x i ^ 2 = 0) →
      ∃ x : Fin m → ℚ, x ≠ 0 ∧ ∑ i, b i * x i ^ 2 = 0) :
    ∃ x : Fin 5 → ℚ, x ≠ 0 ∧ ∑ i, ![1, -1, 2, 3, 5] i * x i ^ 2 = 0 :=
  Rat.exists_diagonal_eq_zero_of_rank_ge_five le_rfl ih _
    (by simp [Fin.forall_fin_succ])
    ⟨![1, 1, 0, 0, 0], fun h => by simpa using congrFun h 0, by simp [Fin.sum_univ_succ]⟩
    fun _ _ => ⟨![1, 1, 0, 0, 0], fun h => by simpa using congrFun h 0,
      by simp [Fin.sum_univ_succ]⟩

/-- The same form in seven variables, `n = 7`. -/
example (ih : ∀ m : ℕ, (m = 7 - 2 ∨ m = 7 - 1) → ∀ b : Fin m → ℚ, (∀ i, b i ≠ 0) →
      (∃ x : Fin m → ℝ, x ≠ 0 ∧ ∑ i, (b i : ℝ) * x i ^ 2 = 0) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin m → ℚ_[p], x ≠ 0 ∧ ∑ i, (b i : ℚ_[p]) * x i ^ 2 = 0) →
      ∃ x : Fin m → ℚ, x ≠ 0 ∧ ∑ i, b i * x i ^ 2 = 0) :
    ∃ x : Fin 7 → ℚ, x ≠ 0 ∧ ∑ i, ![7, -7, 2, 3, 5, 1, 1] i * x i ^ 2 = 0 :=
  Rat.exists_diagonal_eq_zero_of_rank_ge_five (by norm_num) ih _
    (by simp [Fin.forall_fin_succ])
    ⟨![1, 1, 0, 0, 0, 0, 0], fun h => by simpa using congrFun h 0, by simp [Fin.sum_univ_succ]⟩
    fun _ _ => ⟨![1, 1, 0, 0, 0, 0, 0], fun h => by simpa using congrFun h 0,
      by simp [Fin.sum_univ_succ]⟩

end HasseMinkowskiRankFiveTest

