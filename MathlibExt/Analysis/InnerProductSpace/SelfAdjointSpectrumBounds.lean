/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.SelfAdjointSpectrumBounds

/-!
# Spectrum bounds for self-adjoint operators via Rayleigh quotients

For a self-adjoint bounded linear operator `T` on a Hilbert space, every
spectral value `μ` satisfies

  `⨅ x : {x : H // x ≠ 0}, T.rayleighQuotient x ≤ Re μ ≤
   ⨆ x : {x : H // x ≠ 0}, T.rayleighQuotient x`,

i.e. the (real parts of the) spectrum lie between the infimum and the
supremum of the Rayleigh quotient. The proof bounds the norm of a shifted
operator `t • 1 - T` by the length `M - m` of the Rayleigh interval, using
`norm_eq_iSup_rayleighQuotient`, and then applies the resolvent estimate
`spectrum.norm_le_norm_of_mem` to `t - μ ∈ spectrum (t • 1 - T)`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.rayleighQuotient_algebraMap_sub` and
`SpectralTheory.selfAdjoint_spectrum_subset_Icc`
(Theorem, Spectrum Bounds section). The original all-vector interface is
retained as a corollary. The nonzero-vector quotient convention is also
formalized in `v1/Atlas/DifferentialAnalysis/code/SpectralTheoremFix.lean`,
`SpectralTheorem.rayleighInf`, `SpectralTheorem.rayleighSup`, and
`SpectralTheorem.selfAdjoint_spectrum_subset_Icc`.
-/

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Auxiliary lemma: for `t ∈ ℝ` and a nonzero vector `x`, the Rayleigh
quotient of `t • 1 - T` at `x` equals `t` minus the Rayleigh quotient of `T`
at `x`. -/
theorem rayleighQuotient_algebraMap_sub (T : H →L[𝕜] H) (t : ℝ) (x : H) (hx : x ≠ 0) :
    ((algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜) - T).rayleighQuotient x =
      t - T.rayleighQuotient x := by
  unfold ContinuousLinearMap.rayleighQuotient ContinuousLinearMap.reApplyInnerSelf
  simp only [sub_apply, ContinuousLinearMap.algebraMap_apply]
  rw [inner_sub_left, map_sub, inner_smul_left, RCLike.conj_ofReal]
  have h_re_inner : RCLike.re ((↑t : 𝕜) * @inner 𝕜 H _ x x) = t * ‖x‖ ^ 2 := by
    rw [RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, inner_self_eq_norm_sq (𝕜 := 𝕜)]
    simp
  rw [h_re_inner]
  have hxn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

/-- **Spectrum bounds over nonzero vectors.** For a self-adjoint operator
`T` and `μ ∈ Spec(T)`, the real part of `μ` lies between the infimum and
supremum of the Rayleigh quotient over nonzero vectors. -/
theorem selfAdjoint_spectrum_subset_Icc_nonzero [Nontrivial H]
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {mu : 𝕜} (hmu : mu ∈ spectrum 𝕜 T) :
    ⨅ x : {x : H // x ≠ 0}, T.rayleighQuotient x.1 ≤ RCLike.re mu ∧
    RCLike.re mu ≤ ⨆ x : {x : H // x ≠ 0}, T.rayleighQuotient x.1 := by
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  haveI : Nonempty {x : H // x ≠ 0} := by
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    exact ⟨⟨x, hx⟩⟩
  have hrq_bdd : BddAbove (Set.range
      (fun x : {x : H // x ≠ 0} => T.rayleighQuotient x.1)) :=
    ⟨‖T‖, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (T.rayleighQuotient_le_norm x.1)).2⟩
  have hrq_bdd_below : BddBelow (Set.range
      (fun x : {x : H // x ≠ 0} => T.rayleighQuotient x.1)) :=
    ⟨-‖T‖, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (T.rayleighQuotient_le_norm x.1)).1⟩
  set M := ⨆ x : {x : H // x ≠ 0}, T.rayleighQuotient x.1
  set m := ⨅ x : {x : H // x ≠ 0}, T.rayleighQuotient x.1
  have hm_le : ∀ x : H, x ≠ 0 → m ≤ T.rayleighQuotient x :=
    fun x hx => ciInf_le hrq_bdd_below ⟨x, hx⟩
  have hle_M : ∀ x : H, x ≠ 0 → T.rayleighQuotient x ≤ M :=
    fun x hx => le_ciSup hrq_bdd ⟨x, hx⟩
  have hmM : m ≤ M := ciInf_le_ciSup hrq_bdd_below hrq_bdd
  have hshift : ∀ r : 𝕜, ‖r - mu‖ ≤ ‖(algebraMap 𝕜 (H →L[𝕜] H)) r - T‖ := fun r =>
    spectrum.norm_le_norm_of_mem (by
      rw [← spectrum.singleton_sub_eq]; exact Set.sub_mem_sub (Set.mem_singleton r) hmu)
  have h_norm_le : ∀ (t : ℝ), m ≤ t → t ≤ M →
      ‖(algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜) - T‖ ≤ M - m := by
    intro t ht_m ht_M
    have hsa_S : IsSelfAdjoint ((algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜) - T) := by
      have hsa_scalar : IsSelfAdjoint ((algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜)) :=
        IsSelfAdjoint.algebraMap _ (by rw [isSelfAdjoint_iff, RCLike.star_def, RCLike.conj_ofReal])
      exact hsa_scalar.sub hT
    have hsym_S := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa_S
    rw [((algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜) - T).norm_eq_iSup_rayleighQuotient hsym_S]
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · simp [hx, ContinuousLinearMap.rayleighQuotient_apply_zero]
      linarith
    · rw [rayleighQuotient_algebraMap_sub T t x hx]
      rw [abs_le]
      exact ⟨by linarith [hle_M x hx], by linarith [hm_le x hx]⟩
  have h_lower : m ≤ RCLike.re mu := by
    have h1 : ‖(↑M : 𝕜) - mu‖ ≤ M - m :=
      (hshift (↑M : 𝕜)).trans (h_norm_le M hmM le_rfl)
    have h2 : M - RCLike.re mu ≤ ‖(↑M : 𝕜) - mu‖ := by
      have : RCLike.re ((↑M : 𝕜) - mu) = M - RCLike.re mu := by
        simp [map_sub, RCLike.ofReal_re]
      linarith [RCLike.abs_re_le_norm ((↑M : 𝕜) - mu), le_abs_self (RCLike.re ((↑M : 𝕜) - mu))]
    linarith
  have h_upper : RCLike.re mu ≤ M := by
    have h1 : ‖(↑m : 𝕜) - mu‖ ≤ M - m :=
      (hshift (↑m : 𝕜)).trans (h_norm_le m le_rfl hmM)
    have h2 : RCLike.re mu - m ≤ ‖(↑m : 𝕜) - mu‖ := by
      have : RCLike.re ((↑m : 𝕜) - mu) = m - RCLike.re mu := by
        simp [map_sub, RCLike.ofReal_re]
      linarith [RCLike.abs_re_le_norm ((↑m : 𝕜) - mu), neg_abs_le (RCLike.re ((↑m : 𝕜) - mu))]
    linarith
  exact ⟨h_lower, h_upper⟩

/-- The original all-vector spectrum bounds, retained as a corollary of
`selfAdjoint_spectrum_subset_Icc_nonzero`. The all-vector extrema also
include the totalized quotient at zero. -/
theorem selfAdjoint_spectrum_subset_Icc [Nontrivial H]
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {mu : 𝕜} (hmu : mu ∈ spectrum 𝕜 T) :
    ⨅ x : H, T.rayleighQuotient x ≤ RCLike.re mu ∧
    RCLike.re mu ≤ ⨆ x : H, T.rayleighQuotient x := by
  obtain ⟨hl, hu⟩ := selfAdjoint_spectrum_subset_Icc_nonzero T hT hmu
  haveI : Nonempty {x : H // x ≠ 0} := by
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    exact ⟨⟨x, hx⟩⟩
  have hb : BddAbove (Set.range T.rayleighQuotient) :=
    ⟨‖T‖, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (T.rayleighQuotient_le_norm x)).2⟩
  have hb' : BddBelow (Set.range T.rayleighQuotient) :=
    ⟨-‖T‖, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (T.rayleighQuotient_le_norm x)).1⟩
  have h_lower : (⨅ x : H, T.rayleighQuotient x) ≤
      (⨅ x : {x : H // x ≠ 0}, T.rayleighQuotient x.1) :=
    le_ciInf (fun x => ciInf_le hb' x.1)
  have h_upper : (⨆ x : {x : H // x ≠ 0}, T.rayleighQuotient x.1) ≤
      (⨆ x : H, T.rayleighQuotient x) :=
    ciSup_le (fun x => le_ciSup hb x.1)
  exact ⟨h_lower.trans hl, hu.trans h_upper⟩

end MathlibExt.Analysis.InnerProductSpace.SelfAdjointSpectrumBounds
