/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperator

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Spectrum of a diagonal operator on `ℓ²`

For a bounded coefficient sequence `a : ι → 𝕜`, the spectrum of the
diagonal operator `D_a` on `ℓ²(ι, 𝕜)` is the closure of the range of `a`.
This is the spectral counterpart of the norm, adjoint and compactness
results in `LpDiagonalOperator.lean`, and a companion to the Hilbert-space /
spectral material of `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`.
This is a supporting result on the existing bundled Hilbert-basis diagonal API,
specialized to identity coordinates through `LpDiagonalOperator.diagonalCLM`.
The archived source supplies context; this theorem is not identified as a v1 target.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperatorSpectrum

open Filter Topology Set
open scoped _root_.lp
open MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperator

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜]

/-- Subtracting a diagonal operator from a scalar multiple of the identity
gives the diagonal operator with the shifted coefficients. -/
theorem smul_one_sub_diagonalCLM_eq (μ : 𝕜) (a : ι → 𝕜)
    (ha : ∃ C, ∀ i, ‖a i‖ ≤ C) :
    μ • (1 : ℓ²(ι, 𝕜) →L[𝕜] ℓ²(ι, 𝕜)) - diagonalCLM a ha =
      diagonalCLM (fun i => μ - a i) (by
        obtain ⟨C, hC⟩ := ha
        exact ⟨‖μ‖ + C, fun i => (norm_sub_le _ _).trans (add_le_add le_rfl (hC i))⟩) := by
  ext x i
  simp only [sub_apply, smul_apply, one_apply_eq_self, diagonalCLM_apply,
    lp.coeFn_sub, Pi.sub_apply, lp_smul_apply]
  rw [sub_mul]

/-- If `μ` stays a positive distance away from every coefficient, then
`μ • 1 - D_a` is a unit, with inverse the diagonal operator of the
reciprocal coefficients. -/
theorem isUnit_smul_one_sub_diagonalCLM_of_not_mem_closure_range {a : ι → 𝕜}
    (ha : ∃ C, ∀ i, ‖a i‖ ≤ C) {μ : 𝕜} (hμ : μ ∉ closure (Set.range a)) :
    IsUnit (μ • (1 : ℓ²(ι, 𝕜) →L[𝕜] ℓ²(ι, 𝕜)) - diagonalCLM a ha) := by
  rw [Metric.mem_closure_iff] at hμ
  push Not at hμ
  obtain ⟨ε, hε, hε'⟩ := hμ
  have hdist : ∀ i, ε ≤ ‖μ - a i‖ := fun i => by
    have h1 := hε' (a i) ⟨i, rfl⟩
    rwa [dist_eq_norm] at h1
  have hbdd : ∃ C, ∀ i, ‖(μ - a i)⁻¹‖ ≤ C := ⟨ε⁻¹, fun i => by
    rw [norm_inv]
    exact inv_anti₀ hε (hdist i)⟩
  rw [smul_one_sub_diagonalCLM_eq]
  refine isUnit_iff_exists.mpr ⟨diagonalCLM (fun i => (μ - a i)⁻¹) hbdd, ?_, ?_⟩
  · rw [ContinuousLinearMap.mul_def, diagonalCLM_comp]
    have hfun : (fun i => (μ - a i) * (μ - a i)⁻¹) = fun _ => (1 : 𝕜) := by
      funext i
      exact mul_inv_cancel₀ (by
        intro h
        have h1 := hdist i
        rw [h, norm_zero] at h1
        exact not_lt_of_ge h1 hε)
    simp only [hfun]
    exact diagonalCLM_one
  · rw [ContinuousLinearMap.mul_def, diagonalCLM_comp]
    have hfun : (fun i => (μ - a i)⁻¹ * (μ - a i)) = fun _ => (1 : 𝕜) := by
      funext i
      exact inv_mul_cancel₀ (by
        intro h
        have h1 := hdist i
        rw [h, norm_zero] at h1
        exact not_lt_of_ge h1 hε)
    simp only [hfun]
    exact diagonalCLM_one

/-- If `μ` stays a positive distance away from every coefficient, then
`μ` is not in the spectrum of the diagonal operator. -/
theorem not_mem_spectrum_of_not_mem_closure_range {a : ι → 𝕜}
    (ha : ∃ C, ∀ i, ‖a i‖ ≤ C) {μ : 𝕜} (hμ : μ ∉ closure (Set.range a)) :
    μ ∉ spectrum 𝕜 (diagonalCLM a ha) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  exact not_not.mpr (isUnit_smul_one_sub_diagonalCLM_of_not_mem_closure_range ha hμ)

/-- Every coefficient lies in the spectrum of the diagonal operator: the
corresponding coordinate vector is killed by `a j • 1 - D_a`. -/
theorem range_subset_spectrum {a : ι → 𝕜} (ha : ∃ C, ∀ i, ‖a i‖ ≤ C) :
    Set.range a ⊆ spectrum 𝕜 (diagonalCLM a ha) := by
  classical
  rintro μ ⟨j, rfl⟩
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  intro hunit
  have hbij := (ContinuousLinearMap.isUnit_iff_bijective).mp hunit
  have hsingle : (a j • (1 : ℓ²(ι, 𝕜) →L[𝕜] ℓ²(ι, 𝕜)) - diagonalCLM a ha)
      (lp.single 2 j (1 : 𝕜)) = 0 := by
    rw [smul_one_sub_diagonalCLM_eq]
    apply lp.ext
    funext i
    simp only [diagonalCLM_apply, lp.single_apply, lp.coeFn_zero, Pi.zero_apply]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same, sub_self, zero_mul]
    · rw [Pi.single_eq_of_ne hij, mul_zero]
  have h0 : (lp.single 2 j (1 : 𝕜) : ℓ²(ι, 𝕜)) = 0 := hbij.1 (by rw [hsingle]; exact (map_zero _).symm)
  have hn : ‖(lp.single 2 j (1 : 𝕜) : ℓ²(ι, 𝕜))‖ = (1 : ℝ) := by
    rw [lp.norm_single (by norm_num), norm_one]
  rw [h0, norm_zero] at hn
  exact zero_ne_one hn

/-- The spectrum of a diagonal operator on `ℓ²` is the closure of the range
of its coefficients. -/
theorem spectrum_diagonalCLM (a : ι → 𝕜) (ha : ∃ C, ∀ i, ‖a i‖ ≤ C) :
    spectrum 𝕜 (diagonalCLM a ha) = closure (Set.range a) := by
  apply le_antisymm
  · intro μ hμ
    by_contra hnot
    exact not_mem_spectrum_of_not_mem_closure_range ha hnot hμ
  · exact closure_minimal (range_subset_spectrum ha) (spectrum.isClosed _)

end MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperatorSpectrum
