/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.PeierlsBogoliubov

/-!
# Tests for the Peierls–Bogoliubov inequality
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.PeierlsBogoliubov

open MathlibExt.Analysis.InnerProductSpace.PeierlsBogoliubov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The symmetry hypothesis on the convex combination follows from those on `S` and `T`, so the
theorem applies to every pair of symmetric operators. -/
example {n : ℕ} (hn : Module.finrank ℂ E = n) {S T : E →ₗ[ℂ] E} (hS : S.IsSymmetric)
    (hT : T.IsSymmetric) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ∃ hC : ((t : ℂ) • S + ((1 - t : ℝ) : ℂ) • T).IsSymmetric,
      Real.log (∑ j, Real.exp (hC.eigenvalues hn j)) ≤
        t * Real.log (∑ j, Real.exp (hS.eigenvalues hn j)) +
          (1 - t) * Real.log (∑ j, Real.exp (hT.eigenvalues hn j)) := by
  have hC : ((t : ℂ) • S + ((1 - t : ℝ) : ℂ) • T).IsSymmetric :=
    (hS.smul (Complex.conj_ofReal t)).add (hT.smul (Complex.conj_ofReal _))
  exact ⟨hC, log_sum_exp_eigenvalues_convex_comb_le hn hS hT ht₀ ht₁ hC⟩

/-- The multiplicative form at the midpoint `t = 1/2`, on `ℂ²`. -/
example {S T : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)} (hS : S.IsSymmetric)
    (hT : T.IsSymmetric)
    (hC : (((2⁻¹ : ℝ) : ℂ) • S + ((1 - 2⁻¹ : ℝ) : ℂ) • T).IsSymmetric) :
    ∑ j, Real.exp (hC.eigenvalues finrank_euclideanSpace_fin j) ≤
      (∑ j, Real.exp (hS.eigenvalues finrank_euclideanSpace_fin j)) ^ (2⁻¹ : ℝ) *
        (∑ j, Real.exp (hT.eigenvalues finrank_euclideanSpace_fin j)) ^ (1 - 2⁻¹ : ℝ) :=
  sum_exp_eigenvalues_convex_comb_le _ hS hT (by norm_num) (by norm_num) hC

/-- The matrix form, for the noncommuting Pauli matrices `σ_z` and `σ_x` at `t = 1/2`. -/
example : RCLike.re (NormedSpace.exp ((2⁻¹ : ℝ) • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 - 2⁻¹ : ℝ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ))).trace ≤
    RCLike.re (NormedSpace.exp (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)).trace ^ (2⁻¹ : ℝ) *
      RCLike.re (NormedSpace.exp (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)).trace ^
        (1 - 2⁻¹ : ℝ) := by
  refine re_trace_exp_convex_comb_le ?_ ?_ (by norm_num) (by norm_num) <;>
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

end MathlibExtTest.Analysis.InnerProductSpace.PeierlsBogoliubov
