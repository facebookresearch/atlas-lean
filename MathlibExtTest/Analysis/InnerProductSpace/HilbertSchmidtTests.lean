/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.HilbertSchmidt

import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Tests for Hilbert–Schmidt operators on `ℓ²(ℕ, ℂ)`

Concrete checks on `ℓ²(ℕ, ℂ)`:

* the Hilbert–Schmidt operator of the zero matrix is zero;
* the rank-one operator `e₀ ⊗ e₀` (with `e₀ = lp.single 2 0 1`) sends `e₀`
  to itself, kills the `1`-coordinate, has squared Hilbert–Schmidt norm `1`,
  is compact, has matrix `e₀ ⊗ e₀`, and is self-adjoint;
* the diagonal operator with diagonal `1` at `0` and `0` elsewhere sends
  `e₀` to itself, kills the `1`-coordinate, has squared Hilbert–Schmidt
  norm `1`, and has matrix given by the diagonal itself;
* a rank-one operator has operator norm at most `1`.
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.HilbertSchmidtTests

open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open MathlibExt.Analysis.InnerProductSpace.HilbertSchmidt

/-- The zeroth standard basis vector of `ℓ²(ℕ, ℂ)`. -/
private noncomputable abbrev e0 : ℓ²(ℕ, ℂ) := lp.single 2 0 (1 : ℂ)

/-- The Hilbert–Schmidt operator of the zero matrix is zero. -/
private theorem hsOperator_zero_test :
    hsOperator (0 : ℕ → ℕ → ℂ) isHilbertSchmidt_zero = 0 :=
  hsOperator_zero

/-- The rank-one operator `e₀ ⊗ e₀` sends `e₀` to `e₀` at coordinate `0`. -/
private theorem hsRankOne_e0_apply_zero :
    hsOperator (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ)) isHilbertSchmidt_hsRankOne e0 0 = 1 := by
  rw [hsOperator_hsRankOne_apply]
  simp

/-- The rank-one operator `e₀ ⊗ e₀` kills coordinate `1` of `e₀`. -/
private theorem hsRankOne_e0_apply_one :
    hsOperator (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ)) isHilbertSchmidt_hsRankOne e0 1 = 0 := by
  rw [hsOperator_hsRankOne_apply]
  simp

/-- The squared Hilbert–Schmidt norm of `e₀ ⊗ e₀` is `1`. -/
private theorem hsNormSq_hsRankOne_e0 :
    hsNormSq (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ)) isHilbertSchmidt_hsRankOne = 1 := by
  rw [hsNormSq_hsRankOne, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one]
  norm_num

/-- The rank-one operator `e₀ ⊗ e₀` is compact. -/
private theorem isCompactOperator_hsRankOne_e0 :
    IsCompactOperator (hsOperator (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ))
      isHilbertSchmidt_hsRankOne) :=
  isCompactOperator_hsOperator _ _

/-- The matrix of the rank-one operator `e₀ ⊗ e₀` is `e₀ ⊗ e₀` itself. -/
private theorem hsMatrix_hsRankOne_e0 :
    hsMatrix (hsOperator (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ))
      isHilbertSchmidt_hsRankOne) = hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ) :=
  hsMatrix_hsOperator _ _

/-- The conjugate transpose of `e₀ ⊗ e₀` is `e₀ ⊗ e₀` itself. -/
private theorem hsTransposeStar_hsRankOne_e0 :
    hsTransposeStar (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ))
      = hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ) := by
  funext i j
  simp only [hsTransposeStar, hsRankOne, star_mul, star_star]

/-- The rank-one operator `e₀ ⊗ e₀` is self-adjoint. -/
private theorem adjoint_hsRankOne_e0 :
    (hsOperator (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ)) isHilbertSchmidt_hsRankOne)† =
      hsOperator (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ)) isHilbertSchmidt_hsRankOne := by
  rw [adjoint_hsOperator]
  exact hsOperator_congr hsTransposeStar_hsRankOne_e0 _ _

/-- The diagonal with `1` at `0` and `0` elsewhere, as a function `ℕ → ℂ`. -/
private abbrev d0 : ℕ → ℂ := fun n => if n = 0 then 1 else 0

/-- The squared norms of `d0` are summable (it is supported at `0`). -/
private theorem summable_norm_sq_d0 : Summable fun i => ‖d0 i‖ ^ 2 := by
  have h : (fun i => ‖d0 i‖ ^ 2) = fun i => if i = 0 then (1 : ℝ) else 0 := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [d0]
    · simp [d0, hi]
  rw [h]
  have hf : ∀ j, j ≠ 0 → (if j = 0 then (1 : ℝ) else 0) = 0 := fun j hj => ite_eq_right hj
  exact (hasSum_single 0 hf).summable

/-- The diagonal operator with diagonal `d0` sends `e₀` to `e₀` at coordinate `0`. -/
private theorem hsDiagonal_d0_apply_zero :
    hsOperator (hsDiagonal d0) (isHilbertSchmidt_hsDiagonal summable_norm_sq_d0) e0 0 = 1 := by
  rw [hsOperator_hsDiagonal_apply summable_norm_sq_d0]
  simp [d0]

/-- The diagonal operator with diagonal `d0` kills coordinate `1` of `e₀`. -/
private theorem hsDiagonal_d0_apply_one :
    hsOperator (hsDiagonal d0) (isHilbertSchmidt_hsDiagonal summable_norm_sq_d0) e0 1 = 0 := by
  rw [hsOperator_hsDiagonal_apply summable_norm_sq_d0]
  simp [d0]

/-- The squared Hilbert–Schmidt norm of the diagonal matrix `d0` is `1`. -/
private theorem hsNormSq_hsDiagonal_d0 : hsNormSq (hsDiagonal d0) (isHilbertSchmidt_hsDiagonal summable_norm_sq_d0) = 1 := by
  rw [hsNormSq_hsDiagonal summable_norm_sq_d0]
  have h : (fun i => ‖d0 i‖ ^ 2) = fun i => if i = 0 then (1 : ℝ) else 0 := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [d0]
    · simp [d0, hi]
  rw [h]
  simp

/-- The matrix of the diagonal operator with diagonal `d0` is the diagonal itself. -/
private theorem hsMatrix_hsDiagonal_d0 :
    hsMatrix (hsOperator (hsDiagonal d0) (isHilbertSchmidt_hsDiagonal summable_norm_sq_d0))
      = hsDiagonal d0 :=
  hsMatrix_hsOperator _ _

/-- The rank-one operator `e₀ ⊗ e₀` has operator norm at most `1`. -/
private theorem norm_hsRankOne_e0_le :
    ‖hsOperator (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ)) isHilbertSchmidt_hsRankOne‖ ≤ 1 := by
  calc ‖hsOperator (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ)) isHilbertSchmidt_hsRankOne‖
      ≤ Real.sqrt (hsNormSq (hsRankOne (e0 : ℕ → ℂ) (e0 : ℕ → ℂ)) isHilbertSchmidt_hsRankOne) :=
        norm_hsOperator_le _ _
    _ = 1 := by rw [hsNormSq_hsRankOne_e0, Real.sqrt_one]

end MathlibExtTest.Analysis.InnerProductSpace.HilbertSchmidtTests
