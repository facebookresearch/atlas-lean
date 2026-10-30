/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.BergmanSpace

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the Bergman space `A²(𝔻)` and its reproducing kernel

* The Bergman kernel at `0` is the first standard basis vector.
* Evaluation at `0` reads off the constant Taylor coefficient.
* Evaluation of a monomial at `z = 1/2` is `c * √(n + 1) * (1/2)ⁿ`.
* At `z = 1/2`, the kernel has squared norm `16/9` and evaluation has
  norm `4/3`.
* The kernel inner product at `1/2` and `1/3` is `36/25`.
* The kernel inner product at `I/2` and `I/2` is `16/9`.
* Taylor coefficients are inner products with the rescaled monomials.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.BergmanSpaceTests

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open scoped ComplexInnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.BergmanSpace

/-- `0` is in the unit disc. -/
theorem zero_mem_disc : ‖(0 : ℂ)‖ < 1 := by simp

/-- `1/2` is in the unit disc. -/
theorem half_mem_disc : ‖((1 / 2 : ℝ) : ℂ)‖ < 1 := by
  rw [Complex.norm_real]
  norm_num

/-- `1/3` is in the unit disc. -/
theorem third_mem_disc : ‖((1 / 3 : ℝ) : ℂ)‖ < 1 := by
  rw [Complex.norm_real]
  norm_num

/-- `I/2` is in the unit disc. -/
theorem I_div_two_mem_disc : ‖Complex.I / 2‖ < 1 := by
  rw [norm_div, Complex.norm_I]
  norm_num

/-- The Bergman kernel at `0` is the first standard basis vector. -/
example : bergmanKernel (0 : ℂ) zero_mem_disc = lp.single 2 0 (1 : ℂ) :=
  bergmanKernel_zero _

/-- Evaluation at `0` of the second basis vector is `0`. -/
example : bergmanEval (0 : ℂ) zero_mem_disc (lp.single 2 1 (5 : ℂ)) = 0 := by
  rw [bergmanEval_zero]
  simp

/-- Evaluation of the monomial `3 * √3 * z²` at `1/2` is `3 * √3 / 4`. -/
example : bergmanEval ((1 / 2 : ℝ) : ℂ) half_mem_disc (lp.single 2 2 (3 : ℂ)) =
    (3 * Real.sqrt 3 / 4 : ℂ) := by
  rw [bergmanEval_single]
  push_cast
  norm_num
  ring

/-- Evaluation of the monomial `2 * √2 * z` at `1/2` is `√2`. -/
example : bergmanEval ((1 / 2 : ℝ) : ℂ) half_mem_disc (lp.single 2 1 (2 : ℂ)) =
    (Real.sqrt 2 : ℂ) := by
  rw [bergmanEval_single]
  push_cast
  norm_num
  ring

/-- Evaluation of the constant function `3` at `1/2` is `3`. -/
example : bergmanEval ((1 / 2 : ℝ) : ℂ) half_mem_disc (lp.single 2 0 (3 : ℂ)) = 3 := by
  rw [bergmanEval_single]
  simp

/-- At `z = 1/2`, the Bergman kernel has squared norm `16/9`. -/
example : ‖bergmanKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ ^ 2 = 16 / 9 := by
  rw [norm_sq_bergmanKernel, Complex.norm_real]
  norm_num

/-- At `z = 1/2`, the Bergman kernel has norm `4/3`. -/
example : ‖bergmanKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ = 4 / 3 := by
  rw [norm_bergmanKernel, Complex.norm_real]
  norm_num

/-- At `z = 1/2`, point evaluation has norm `4/3`. -/
example : ‖bergmanEvalCLM ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ = 4 / 3 := by
  rw [norm_bergmanEvalCLM, Complex.norm_real]
  norm_num

/-- The kernel inner product at `1/2` and `1/3` is `36/25`. -/
example : ⟪bergmanKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc,
    bergmanKernel ((1 / 3 : ℝ) : ℂ) third_mem_disc⟫ = 36 / 25 := by
  rw [inner_bergmanKernel_bergmanKernel, Complex.conj_ofReal]
  push_cast
  norm_num

/-- The kernel inner product at `I/2` and `I/2` is `16/9`. -/
example : ⟪bergmanKernel (Complex.I / 2) I_div_two_mem_disc,
    bergmanKernel (Complex.I / 2) I_div_two_mem_disc⟫ = 16 / 9 := by
  have hconj : (starRingEnd ℂ) (Complex.I / 2) = -(Complex.I / 2) := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
    ring
  have hI : (1 : ℂ) - Complex.I / 2 * (-(Complex.I / 2)) = 3 / 4 := by
    rw [mul_neg, div_mul_div_comm, Complex.I_mul_I]
    norm_num
  rw [inner_bergmanKernel_bergmanKernel, hconj, hI]
  norm_num

/-- Evaluation of the kernel at its own point `1/2` is `16/9`. -/
example : bergmanEval ((1 / 2 : ℝ) : ℂ) half_mem_disc
    (bergmanKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc) = 16 / 9 := by
  rw [bergmanEval_bergmanKernel]
  norm_num

/-- The rescaled monomials are orthonormal: `⟪e₁, e₁⟫ = 1`. -/
example : ⟪(lp.single 2 1 (1 : ℂ) : ℓ²(ℕ, ℂ)), (lp.single 2 1 (1 : ℂ) : ℓ²(ℕ, ℂ))⟫_ℂ = 1 :=
  by rw [bergmanMonomial_orthonormal]; simp

/-- The rescaled monomials are orthonormal: `⟪e₁, e₂⟫ = 0`. -/
example : ⟪(lp.single 2 1 (1 : ℂ) : ℓ²(ℕ, ℂ)), (lp.single 2 2 (1 : ℂ) : ℓ²(ℕ, ℂ))⟫_ℂ = 0 :=
  by rw [bergmanMonomial_orthonormal]; simp

/-- The third coefficient of `2 * e₃` is `2`. -/
example : (lp.single 2 3 (2 : ℂ) : ℓ²(ℕ, ℂ)) 3 =
    ⟪(lp.single 2 3 (1 : ℂ) : ℓ²(ℕ, ℂ)), (lp.single 2 3 (2 : ℂ) : ℓ²(ℕ, ℂ))⟫ :=
  bergmanCoeff_eq_inner _ _

/-- The Taylor series of an `A²` function converges absolutely at `1/2`. -/
example (a : ℓ²(ℕ, ℂ)) :
    Summable (fun n => a n * (Real.sqrt ((n : ℝ) + 1) : ℂ) * (((1 / 2 : ℝ) : ℂ)) ^ n) :=
  summable_bergmanEval_terms ((1 / 2 : ℝ) : ℂ) half_mem_disc a

/-- The named monomial family satisfies Mathlib's standard orthonormal
predicate. -/
example : Orthonormal ℂ bergmanMonomial :=
  orthonormal_bergmanMonomial

/-- Standard orthonormal-family APIs establish linear independence. -/
example : LinearIndependent ℂ bergmanMonomial :=
  orthonormal_bergmanMonomial.linearIndependent

/-- The named family evaluates to the normalized monomials. -/
example (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) :
    bergmanEval z hz (bergmanMonomial n) =
      (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ n := by
  simpa [bergmanMonomial] using bergmanEval_single z hz n (1 : ℂ)

end MathlibExtTest.Analysis.InnerProductSpace.BergmanSpaceTests
