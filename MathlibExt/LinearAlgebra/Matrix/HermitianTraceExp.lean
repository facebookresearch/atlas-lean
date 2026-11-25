/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# The trace exponential of a Hermitian matrix and its extreme eigenvalues

For a Hermitian matrix `A` with eigenvalues `λ₁, …, λ_d` and a real number `θ`, the matrix
exponential `e^{θA}` (the power series `NormedSpace.exp`) is the standard matrix function of
`a ↦ e^{θa}`, so `tr e^{θA} = ∑ᵢ e^{θλᵢ}`. Every term of this sum is positive, hence each
`e^{θλᵢ}` is at most `tr e^{θA}`. Applied to the largest eigenvalue this is
`e^{λmax(θA)} = λmax(e^{θA}) ≤ tr e^{θA}`, the deterministic step of the matrix Laplace
transform method (J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*, Found.
Trends Mach. Learn. 8 (2015), arXiv:1501.01571, display (3.2.3)); the same bound for `θ < 0` and
the smallest eigenvalue gives the lower tail.

## Main declarations

* `Matrix.IsHermitian.trace_cfc_eq_sum` : `tr f(A) = ∑ᵢ f(λᵢ)` for the functional calculus.
* `Matrix.IsHermitian.exp_smul_eq_cfc` : `e^{θA}` is the standard matrix function of `e^{θ·}`.
* `Matrix.IsHermitian.trace_exp_smul_eq_sum` : `tr e^{θA} = ∑ᵢ e^{θλᵢ}`.
* `Matrix.IsHermitian.lambdaMax`, `Matrix.IsHermitian.lambdaMin` : extreme eigenvalues.
* `Matrix.IsHermitian.exp_mul_lambdaMax_le_re_trace_exp`,
  `Matrix.IsHermitian.exp_mul_lambdaMin_le_re_trace_exp` : `e^{θ λ} ≤ tr e^{θA}`.
* `Matrix.PosSemidef.eigenvalues_le_re_trace` : `λᵢ(A) ≤ tr A` for `A ⪰ 0` (Tropp (2.1.13)).
-/

@[expose] public section

open scoped BigOperators
open NormedSpace
open scoped ComplexOrder

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

namespace IsHermitian

/-- **Trace of a standard matrix function.** For a Hermitian matrix `A` and any `f : ℝ → ℝ`,
`tr f(A) = ∑ᵢ f(λᵢ(A))`, where `f(A)` is the continuous functional calculus (Tropp,
*An Introduction to Matrix Concentration Inequalities*, arXiv:1501.01571, Definition 2.1.2 and
Proposition 2.1.3). -/
theorem trace_cfc_eq_sum (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : 𝕜) := by
  have hsplit : (cfc f A).charpoly.Splits := by
    rw [hA.charpoly_cfc_eq f]
    exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
  rw [trace_eq_sum_roots_charpoly_of_splits hsplit, hA.charpoly_cfc_eq f,
    Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _)]
  simp

/-- **The matrix exponential is a standard matrix function.** For a Hermitian matrix `A` and a
real `θ`, the power-series exponential `e^{θA}` equals the functional calculus of
`a ↦ e^{θa}` (Tropp, arXiv:1501.01571, display (2.1.15)). Mathlib's
`CFC.real_exp_eq_normedSpace_exp` gives this in a normed algebra; `Matrix` carries no global
norm, so the statement is proved here directly from the spectral theorem. -/
theorem exp_smul_eq_cfc (hA : A.IsHermitian) (θ : ℝ) :
    NormedSpace.exp (θ • A) = cfc (fun x => Real.exp (θ * x)) A := by
  rw [hA.cfc_eq, IsHermitian.cfc]
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  have hUnit : IsUnit U := (Unitary.toUnits hA.eigenvectorUnitary).isUnit
  have hinv : U⁻¹ = star U := by
    rw [hU]
    exact Matrix.inv_eq_left_inv (Unitary.coe_star_mul_self hA.eigenvectorUnitary)
  have hθA : θ • A = U * diagonal (fun i => ((θ * hA.eigenvalues i : ℝ) : 𝕜)) * U⁻¹ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [hinv, Unitary.conjStarAlgAut_apply, ← smul_mul_assoc, ← mul_smul_comm,
      ← diagonal_smul]
    congr 3
    funext i
    simp [RCLike.real_smul_eq_coe_mul]
  rw [hθA, Matrix.exp_conj _ _ hUnit, Matrix.exp_diagonal, hinv, Unitary.conjStarAlgAut_apply]
  have hv : (NormedSpace.exp fun i => ((θ * hA.eigenvalues i : ℝ) : 𝕜)) =
      RCLike.ofReal ∘ (fun x => Real.exp (θ * x)) ∘ hA.eigenvalues := by
    rw [Pi.exp_def]
    funext i
    have := map_exp (algebraMap ℝ 𝕜) (continuous_algebraMap ℝ 𝕜) (θ * hA.eigenvalues i)
    simp only [RCLike.algebraMap_eq_ofReal] at this
    simp only [Function.comp_apply, Real.exp_eq_exp_ℝ, this]
  rw [hv]

/-- **Trace exponential in terms of eigenvalues.** For a Hermitian matrix `A` and a real `θ`,
`tr e^{θA} = ∑ᵢ e^{θλᵢ(A)}` (Tropp, arXiv:1501.01571, §2.1.11). -/
theorem trace_exp_smul_eq_sum (hA : A.IsHermitian) (θ : ℝ) :
    (NormedSpace.exp (θ • A)).trace = ∑ i, (Real.exp (θ * hA.eigenvalues i) : 𝕜) := by
  rw [hA.exp_smul_eq_cfc θ, hA.trace_cfc_eq_sum]

/-- **Real trace exponential in terms of eigenvalues.** For a Hermitian `A` and a real `θ`, the
real part of `tr e^{θA}` is `∑ᵢ e^{θλᵢ(A)}` (Tropp, arXiv:1501.01571, §2.1.11). -/
theorem re_trace_exp_smul_eq_sum (hA : A.IsHermitian) (θ : ℝ) :
    RCLike.re (NormedSpace.exp (θ • A)).trace = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  rw [hA.trace_exp_smul_eq_sum θ, map_sum]
  simp

/-- **Trace exponential dominates each eigenvalue.** For a Hermitian `A`, a real `θ` and each
index `i`, `e^{θλᵢ(A)} ≤ tr e^{θA}`, since every term of `∑ⱼ e^{θλⱼ(A)}` is positive (Tropp,
arXiv:1501.01571, proof of display (3.2.3)). -/
theorem exp_mul_eigenvalues_le_re_trace_exp (hA : A.IsHermitian) (θ : ℝ) (i : n) :
    Real.exp (θ * hA.eigenvalues i) ≤ RCLike.re (NormedSpace.exp (θ • A)).trace := by
  rw [hA.re_trace_exp_smul_eq_sum θ]
  exact Finset.single_le_sum (f := fun j => Real.exp (θ * hA.eigenvalues j))
    (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

/-- **Positivity of the trace exponential.** For a Hermitian matrix `A` of positive dimension
and a real `θ`, `tr e^{θA} > 0` (Tropp, arXiv:1501.01571, §2.1.11: `e^{θA}` is positive
definite). -/
theorem re_trace_exp_pos [Nonempty n] (hA : A.IsHermitian) (θ : ℝ) :
    0 < RCLike.re (NormedSpace.exp (θ • A)).trace :=
  (Real.exp_pos _).trans_le (hA.exp_mul_eigenvalues_le_re_trace_exp θ (Classical.arbitrary n))

/-- **Nonnegativity of the trace exponential.** For a Hermitian matrix `A` and a real `θ`,
`tr e^{θA} ≥ 0` (Tropp, arXiv:1501.01571, §2.1.11). -/
theorem re_trace_exp_nonneg (hA : A.IsHermitian) (θ : ℝ) :
    0 ≤ RCLike.re (NormedSpace.exp (θ • A)).trace := by
  rw [hA.re_trace_exp_smul_eq_sum θ]
  exact Finset.sum_nonneg fun j _ => (Real.exp_pos _).le

/-- **Largest eigenvalue.** `λmax(A)`, the largest eigenvalue of a Hermitian matrix `A` on a
nonempty index type (Tropp, arXiv:1501.01571, §2.1.6). -/
noncomputable def lambdaMax [Nonempty n] (hA : A.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues

/-- **Smallest eigenvalue.** `λmin(A)`, the smallest eigenvalue of a Hermitian matrix `A` on
a nonempty index type (Tropp, arXiv:1501.01571, §2.1.6). -/
noncomputable def lambdaMin [Nonempty n] (hA : A.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues

/-- **Every eigenvalue is at most `λmax`.** For a Hermitian `A`, `λᵢ(A) ≤ λmax(A)` for every
index `i`. -/
theorem eigenvalues_le_lambdaMax [Nonempty n] (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i ≤ hA.lambdaMax :=
  Finset.le_sup' hA.eigenvalues (Finset.mem_univ i)

/-- **Every eigenvalue is at least `λmin`.** For a Hermitian `A`, `λmin(A) ≤ λᵢ(A)` for every
index `i`. -/
theorem lambdaMin_le_eigenvalues [Nonempty n] (hA : A.IsHermitian) (i : n) :
    hA.lambdaMin ≤ hA.eigenvalues i :=
  Finset.inf'_le hA.eigenvalues (Finset.mem_univ i)

/-- **`λmax` is attained.** For a Hermitian `A`, `λmax(A)` is one of the eigenvalues
`λᵢ(A)`. -/
theorem exists_eigenvalues_eq_lambdaMax [Nonempty n] (hA : A.IsHermitian) :
    ∃ i, hA.eigenvalues i = hA.lambdaMax := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hA.eigenvalues
  exact ⟨i, hi.symm⟩

/-- **`λmin` is attained.** For a Hermitian `A`, `λmin(A)` is one of the eigenvalues
`λᵢ(A)`. -/
theorem exists_eigenvalues_eq_lambdaMin [Nonempty n] (hA : A.IsHermitian) :
    ∃ i, hA.eigenvalues i = hA.lambdaMin := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hA.eigenvalues
  exact ⟨i, hi.symm⟩

/-- **`λmin ≤ λmax`.** For a Hermitian `A` of positive dimension, `λmin(A) ≤ λmax(A)`. -/
theorem lambdaMin_le_lambdaMax [Nonempty n] (hA : A.IsHermitian) :
    hA.lambdaMin ≤ hA.lambdaMax :=
  (hA.lambdaMin_le_eigenvalues (Classical.arbitrary n)).trans
    (hA.eigenvalues_le_lambdaMax _)

/-- **Trace exponential dominates the top eigenvalue.** For a Hermitian `A` and any real `θ`,
`e^{θ λmax(A)} ≤ tr e^{θA}`; for `θ > 0` this is `e^{λmax(θA)} = λmax(e^{θA}) ≤ tr e^{θA}`
(Tropp, arXiv:1501.01571, display (3.2.3)). -/
theorem exp_mul_lambdaMax_le_re_trace_exp [Nonempty n] (hA : A.IsHermitian) (θ : ℝ) :
    Real.exp (θ * hA.lambdaMax) ≤ RCLike.re (NormedSpace.exp (θ • A)).trace := by
  obtain ⟨i, hi⟩ := hA.exists_eigenvalues_eq_lambdaMax
  rw [← hi]
  exact hA.exp_mul_eigenvalues_le_re_trace_exp θ i

/-- **Trace exponential dominates the bottom eigenvalue.** For a Hermitian `A` and any real
`θ`, `e^{θ λmin(A)} ≤ tr e^{θA}`; for `θ < 0` this is the step behind the lower tail bound of
Tropp, arXiv:1501.01571, Proposition 3.2.1, display (3.2.2). -/
theorem exp_mul_lambdaMin_le_re_trace_exp [Nonempty n] (hA : A.IsHermitian) (θ : ℝ) :
    Real.exp (θ * hA.lambdaMin) ≤ RCLike.re (NormedSpace.exp (θ • A)).trace := by
  obtain ⟨i, hi⟩ := hA.exists_eigenvalues_eq_lambdaMin
  rw [← hi]
  exact hA.exp_mul_eigenvalues_le_re_trace_exp θ i

end IsHermitian

namespace PosSemidef

/-- **The trace dominates each eigenvalue of a positive-semidefinite matrix**: `λᵢ(A) ≤ tr A`
when `A ⪰ 0`, in particular `λmax(A) ≤ tr A` (Tropp, arXiv:1501.01571, display (2.1.13)). -/
theorem eigenvalues_le_re_trace (hA : A.PosSemidef) (i : n) :
    hA.1.eigenvalues i ≤ RCLike.re A.trace := by
  rw [hA.1.trace_eq_sum_eigenvalues, map_sum]
  simp only [RCLike.ofReal_re]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

end PosSemidef

end Matrix
