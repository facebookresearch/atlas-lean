/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.FockSpace

import MathlibExt.Analysis.InnerProductSpace.HardySpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the Fock space and its reproducing kernel

* The Fock kernel at `0` is the first standard basis vector.
* Evaluation at `0` reads off the constant Taylor coefficient.
* Evaluation of a monomial at `z = 1/2` is `c * (1/2)ⁿ / √(n!)`.
* At `z = 1/2`, the kernel has squared norm `Real.exp (1/4)` and
  evaluation has norm `Real.exp (1/8)`.
* The kernel inner product at `1/2` and `I/2` is `Complex.exp (-I/4)`.
* The kernel inner product at `1/2` and `1/2` is `Real.exp (1/4)`.
* Coherent states are unit vectors, and the overlap of the coherent
  states at `0` and `1` is `Real.exp (-1/2)` (Gaussian).
* Taylor coefficients are inner products with the rescaled monomials.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.FockSpaceTests

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open scoped ComplexInnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.FockSpace

/-- The Fock kernel at `0` is the first standard basis vector. -/
example : fockKernel (0 : ℂ) = lp.single 2 0 (1 : ℂ) :=
  fockKernel_zero

/-- Evaluation at `0` of the second basis vector is `0`. -/
example : fockEval (0 : ℂ) (lp.single 2 1 (5 : ℂ)) = 0 := by
  rw [fockEval_zero]
  simp

/-- Evaluation of the monomial `3 * z² / √2` at `1/2` is `3 / (4 * √2)`. -/
example : fockEval ((1 / 2 : ℝ) : ℂ) (lp.single 2 2 (3 : ℂ)) =
    (3 * ((1 / 2 : ℝ) : ℂ) ^ 2 / (Real.sqrt 2 : ℂ)) := by
  rw [fockEval_single]
  norm_num [Nat.factorial]

/-- Evaluation of the constant function `3` at `1/2` is `3`. -/
example : fockEval ((1 / 2 : ℝ) : ℂ) (lp.single 2 0 (3 : ℂ)) = 3 := by
  rw [fockEval_single]
  simp

/-- At `z = 1/2`, the Fock kernel has squared norm `Real.exp (1/4)`. -/
example : ‖fockKernel ((1 / 2 : ℝ) : ℂ)‖ ^ 2 = Real.exp (1 / 4) := by
  rw [norm_sq_fockKernel, Complex.norm_real]
  norm_num

/-- At `z = 1/2`, the Fock kernel has norm `Real.exp (1/8)`. -/
example : ‖fockKernel ((1 / 2 : ℝ) : ℂ)‖ = Real.exp (1 / 8) := by
  rw [norm_fockKernel, Complex.norm_real]
  norm_num

/-- At `z = 1/2`, point evaluation has norm `Real.exp (1/8)`. -/
example : ‖fockEvalCLM ((1 / 2 : ℝ) : ℂ)‖ = Real.exp (1 / 8) := by
  rw [norm_fockEvalCLM, Complex.norm_real]
  norm_num

/-- The kernel inner product at `1/2` and `1/2` is `Real.exp (1/4)`. -/
example : ⟪fockKernel ((1 / 2 : ℝ) : ℂ), fockKernel ((1 / 2 : ℝ) : ℂ)⟫ =
    ((Real.exp (1 / 4) : ℝ) : ℂ) := by
  have h : ((1 / 2 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) = ((1 / 4 : ℝ) : ℂ) := by
    push_cast
    norm_num
  rw [inner_fockKernel_fockKernel, Complex.conj_ofReal, h, Complex.ofReal_exp]

/-- The kernel inner product at `1/2` and `I/2` is `Complex.exp (-I/4)`. -/
example : ⟪fockKernel ((1 / 2 : ℝ) : ℂ), fockKernel (Complex.I / 2)⟫ =
    Complex.exp (-(Complex.I / 4)) := by
  rw [inner_fockKernel_fockKernel]
  have hconj : (starRingEnd ℂ) (Complex.I / 2) = -(Complex.I / 2) := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
    ring
  rw [hconj]
  congr 1
  push_cast
  ring

/-- Evaluation of the kernel at its own point `1/2` is `Real.exp (1/4)`. -/
example : fockEval ((1 / 2 : ℝ) : ℂ) (fockKernel ((1 / 2 : ℝ) : ℂ)) =
    ((Real.exp (1 / 4) : ℝ) : ℂ) := by
  rw [fockEval_fockKernel, Complex.norm_real]
  norm_num

/-- The coherent state at `0` is the first standard basis vector. -/
example : fockCoherent (0 : ℂ) = lp.single 2 0 (1 : ℂ) := by
  unfold fockCoherent
  rw [fockKernel_zero]
  simp

/-- Coherent states are unit vectors: `‖ĉ_{1/2}‖ = 1`. -/
example : ‖fockCoherent ((1 / 2 : ℝ) : ℂ)‖ = 1 :=
  norm_fockCoherent _

/-- The overlap of the coherent states at `0` and `1` is
`Real.exp (-1/2)`, a Gaussian. -/
example : ‖⟪fockCoherent (0 : ℂ), fockCoherent (1 : ℂ)⟫‖ = Real.exp (-1 / 2) := by
  have hnorm : ‖(0 : ℂ) - (1 : ℂ)‖ = 1 := by simp
  rw [norm_inner_fockCoherent_fockCoherent, hnorm]
  norm_num

/-- The rescaled monomials are orthonormal: `⟪e₁, e₁⟫ = 1`. -/
example : ⟪(lp.single 2 1 (1 : ℂ) : ℓ²(ℕ, ℂ)), (lp.single 2 1 (1 : ℂ) : ℓ²(ℕ, ℂ))⟫_ℂ = 1 :=
  by rw [fockMonomial_orthonormal]; simp

/-- The rescaled monomials are orthonormal: `⟪e₁, e₂⟫ = 0`. -/
example : ⟪(lp.single 2 1 (1 : ℂ) : ℓ²(ℕ, ℂ)), (lp.single 2 2 (1 : ℂ) : ℓ²(ℕ, ℂ))⟫_ℂ = 0 :=
  by rw [fockMonomial_orthonormal]; simp

/-- The third coefficient of `2 * e₃` is `2`. -/
example : (lp.single 2 3 (2 : ℂ) : ℓ²(ℕ, ℂ)) 3 =
    ⟪(lp.single 2 3 (1 : ℂ) : ℓ²(ℕ, ℂ)), (lp.single 2 3 (2 : ℂ) : ℓ²(ℕ, ℂ))⟫ :=
  fockCoeff_eq_inner _ _

/-- The Taylor series of a Fock-space function converges absolutely at `1/2`. -/
example (a : ℓ²(ℕ, ℂ)) :
    Summable (fun n => a n * (((1 / 2 : ℝ) : ℂ)) ^ n /
      (Real.sqrt (Nat.factorial n : ℝ) : ℂ)) :=
  summable_fockEval_terms ((1 / 2 : ℝ) : ℂ) a

/-- The named normalized monomials support standard family consequences. -/
theorem linearIndependent_fockMonomial : LinearIndependent ℂ fockMonomial :=
  orthonormal_fockMonomial.linearIndependent

section CanonicalCoefficientRegression

open MathlibExt.Analysis.InnerProductSpace.HardySpace

/-- Explicitly importing Hardy leaves one coefficient bound when both namespaces are open. -/
example (a : ℓ²(ℕ, ℂ)) (n : ℕ) : ‖a n‖ ≤ ‖a‖ :=
  abs_coeff_le_norm a n

end CanonicalCoefficientRegression

/-- Coefficients are extracted through the named normalized Fock monomials. -/
example (a : ℓ²(ℕ, ℂ)) (n : ℕ) : a n = ⟪fockMonomial n, a⟫ :=
  fockCoeff_eq_inner a n

#print axioms MathlibExt.Analysis.InnerProductSpace.FockSpace.norm_fockKernel
#print axioms MathlibExt.Analysis.InnerProductSpace.FockSpace.inner_fockKernel_fockKernel
#print axioms MathlibExt.Analysis.InnerProductSpace.FockSpace.norm_fockEvalCLM
#print axioms MathlibExt.Analysis.InnerProductSpace.FockSpace.norm_inner_fockCoherent_fockCoherent

end MathlibExtTest.Analysis.InnerProductSpace.FockSpaceTests
