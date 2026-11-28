/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Normed.Algebra.Spectrum

@[expose] public section

open ContinuousLinearMap
open scoped InnerProductSpace
open scoped NNReal

namespace MathlibExt.Analysis.InnerProductSpace.SelfAdjointPositiveSpectrum

/-!
# Positivity of a self-adjoint operator iff its spectrum is nonnegative

For a self-adjoint bounded linear operator `T` on a Hilbert space,
`⟨Tu, u⟩ ≥ 0` for every `u` if and only if every spectral value of `T`
has nonnegative real part.

The forward direction is proved from Mathlib's unit criterion
`ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`: if `Re μ < 0`
then `μ • 1 - T` satisfies the lower bound
`‖x‖² (-Re μ) ≤ ‖⟪(μ • 1 - T) x, x⟫‖`, so it is a unit and `μ` is not
in the spectrum. The reverse direction follows the textbook argument:
if the infimum `m` of the Rayleigh quotient were negative, the shifted
operator `S = M • 1 - T` (with `M` the supremum of the Rayleigh quotient)
has nonnegative Rayleigh quotient, hence nonnegative spectrum by the
forward direction, but `‖S‖` or `-‖S‖` lies in the spectrum of `S` by
Mathlib's `abs_rayleighQuotient_le_of_norm_mem_resolventSet`, which
forces `‖S‖ ≤ M`, contradicting `‖S‖ > M` (witnessed by a vector with
negative Rayleigh quotient).

This module is self-contained against the base commit: it does not use
Batch 5's `selfAdjoint_spectrum_subset_Icc`, and the two computational
helpers below are kept private.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.positive_iff_spectrum_nonneg` (Corollary, May 6, 2021).
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The real part of `⟪Tx, x⟫` is the Rayleigh quotient of `T` at `x`
times `‖x‖²`. -/
private theorem reApplyInnerSelf_eq_rayleighQuotient_mul (T : H →L[𝕜] H) (x : H) :
    T.reApplyInnerSelf x = T.rayleighQuotient x * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · subst hx
    simp [ContinuousLinearMap.rayleighQuotient_apply_zero,
      ContinuousLinearMap.reApplyInnerSelf_apply]
  · rw [ContinuousLinearMap.rayleighQuotient]
    field_simp [norm_ne_zero_iff.mpr hx]

omit [CompleteSpace H] in
/-- The Rayleigh quotient of a real scalar operator at a nonzero vector
is the scalar. -/
private theorem rayleighQuotient_algebraMap_ofReal (t : ℝ) (x : H) (hx : x ≠ 0) :
    ((algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜)).rayleighQuotient x = t := by
  have h1 : ((algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜)).reApplyInnerSelf x = t * ‖x‖ ^ 2 := by
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.algebraMap_apply,
      inner_smul_left, inner_self_eq_norm_sq_to_K, RCLike.mul_re, RCLike.conj_ofReal]
  rw [ContinuousLinearMap.rayleighQuotient, h1]
  field_simp [norm_ne_zero_iff.mpr hx]

/-- **Spectrum of an accretive operator has nonnegative real part.** Let $T$ be a bounded linear
operator on a Hilbert space $H$ over $\mathbb{R}$ or $\mathbb{C}$. If
$\operatorname{Re}\langle Tu, u\rangle \ge 0$ for every $u \in H$, then every element $\mu$ of
the spectrum of $T$ satisfies $\operatorname{Re}\mu \ge 0$. -/
theorem spectrum_re_nonneg_of_reApplyInnerSelf_nonneg {T : H →L[𝕜] H}
    (hpos : ∀ u : H, 0 ≤ T.reApplyInnerSelf u) :
    ∀ μ ∈ spectrum 𝕜 T, 0 ≤ RCLike.re μ := by
  intro μ hμ
  by_contra hneg
  have hneg' : RCLike.re μ < 0 := lt_of_not_ge hneg
  have hunit : IsUnit ((algebraMap 𝕜 (H →L[𝕜] H)) μ - T) := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
      (c := (⟨-RCLike.re μ, le_of_lt (neg_pos.mpr hneg')⟩ : ℝ≥0))
    · exact_mod_cast neg_pos.mpr hneg'
    · intro x
      have hre : RCLike.re ⟪((algebraMap 𝕜 (H →L[𝕜] H)) μ - T) x, x⟫_𝕜
          = RCLike.re μ * ‖x‖ ^ 2 - T.reApplyInnerSelf x := by
        have h1 : ⟪((algebraMap 𝕜 (H →L[𝕜] H)) μ - T) x, x⟫_𝕜
            = (starRingEnd 𝕜) μ * (‖x‖ ^ 2 : 𝕜) - ⟪T x, x⟫_𝕜 := by
          simp [sub_apply, ContinuousLinearMap.algebraMap_apply, inner_sub_left, inner_smul_left]
        rw [h1, map_sub, ContinuousLinearMap.reApplyInnerSelf_apply]
        have h2 : RCLike.re ((starRingEnd 𝕜) μ * (‖x‖ ^ 2 : 𝕜)) = RCLike.re μ * ‖x‖ ^ 2 := by
          rw [RCLike.mul_re]
          simp [RCLike.conj_re, RCLike.conj_im]
        rw [h2]
      have h1 : -RCLike.re ⟪((algebraMap 𝕜 (H →L[𝕜] H)) μ - T) x, x⟫_𝕜
          ≤ ‖⟪((algebraMap 𝕜 (H →L[𝕜] H)) μ - T) x, x⟫_𝕜‖ :=
        (neg_le_abs _).trans (RCLike.abs_re_le_norm _)
      rw [hre] at h1
      have hposx := hpos x
      show ‖x‖ ^ 2 * (-RCLike.re μ) ≤ ‖⟪((algebraMap 𝕜 (H →L[𝕜] H)) μ - T) x, x⟫_𝕜‖
      linarith [h1, hposx]
  exact (spectrum.mem_iff.mp hμ) hunit

/-- **Positivity iff spectrum nonnegative.** Let $T$ be a self-adjoint bounded linear operator on a
nonzero Hilbert space $H$ over $\mathbb{R}$ or $\mathbb{C}$. Then
$\operatorname{Re}\langle Tu, u\rangle \ge 0$ for every $u \in H$ if and only if every element
$\mu$ of the spectrum of $T$ satisfies $\operatorname{Re}\mu \ge 0$. -/
theorem positive_iff_spectrum_nonneg [Nontrivial H] (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) :
    (∀ u : H, 0 ≤ T.reApplyInnerSelf u) ↔
    (∀ μ ∈ spectrum 𝕜 T, 0 ≤ RCLike.re μ) := by
  constructor
  · exact spectrum_re_nonneg_of_reApplyInnerSelf_nonneg
  · intro hspec u
    by_cases hu : u = 0
    · subst hu
      simp [ContinuousLinearMap.reApplyInnerSelf_apply]
    · have hrq_bdd : BddAbove (Set.range T.rayleighQuotient) :=
        ⟨‖T‖, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (T.rayleighQuotient_le_norm x)).2⟩
      have hrq_bdd_below : BddBelow (Set.range T.rayleighQuotient) :=
        ⟨-‖T‖, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (T.rayleighQuotient_le_norm x)).1⟩
      set M := ⨆ x : H, T.rayleighQuotient x with hM_def
      set m := ⨅ x : H, T.rayleighQuotient x with hm_def
      have hm_le : ∀ x, m ≤ T.rayleighQuotient x := fun x => ciInf_le hrq_bdd_below x
      have hle_M : ∀ x, T.rayleighQuotient x ≤ M := fun x => le_ciSup hrq_bdd x
      rw [reApplyInnerSelf_eq_rayleighQuotient_mul]
      apply mul_nonneg _ (sq_nonneg _)
      suffices hm_nonneg : 0 ≤ m from le_trans hm_nonneg (hm_le u)
      by_contra h_m_neg
      have h_m_neg' : m < 0 := lt_of_not_ge h_m_neg
      set S := (algebraMap 𝕜 (H →L[𝕜] H)) (↑M : 𝕜) - T with hS_def
      have hS_sa : IsSelfAdjoint S :=
        (IsSelfAdjoint.algebraMap _
          (by rw [isSelfAdjoint_iff, RCLike.star_def, RCLike.conj_ofReal])).sub hT
      have hS_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS_sa
      have hS_rq : ∀ x : H, x ≠ 0 → S.rayleighQuotient x = M - T.rayleighQuotient x := by
        intro x hx
        rw [hS_def, sub_eq_add_neg, ContinuousLinearMap.rayleighQuotient_add,
          ContinuousLinearMap.rayleighQuotient_neg_apply, rayleighQuotient_algebraMap_ofReal M x hx,
          sub_eq_add_neg]
      have hS_rq_nonneg : ∀ x : H, 0 ≤ S.rayleighQuotient x := by
        intro x
        by_cases hx : x = 0
        · rw [hx, ContinuousLinearMap.rayleighQuotient_apply_zero]
        · rw [hS_rq x hx]; linarith [hle_M x]
      have hS_pos : ∀ x : H, 0 ≤ S.reApplyInnerSelf x := by
        intro x
        rw [reApplyInnerSelf_eq_rayleighQuotient_mul]
        exact mul_nonneg (hS_rq_nonneg x) (sq_nonneg _)
      have hS_ne : S ≠ 0 := by
        intro hS_eq
        have hS_zero : (S : H →L[𝕜] H) = 0 := hS_eq
        have hT_scalar : T = (algebraMap 𝕜 (H →L[𝕜] H)) (↑M : 𝕜) := by
          have h : S = (algebraMap 𝕜 (H →L[𝕜] H)) (↑M : 𝕜) - T := rfl
          rw [hS_zero, eq_comm, sub_eq_zero] at h; exact h.symm
        have hM_in_spec : (↑M : 𝕜) ∈ spectrum 𝕜 T := by
          rw [hT_scalar, spectrum.mem_iff]; simp only [sub_self, not_isUnit_zero, not_false_eq_true]
        have hM_nonneg : (0 : ℝ) ≤ M := by
          have := hspec _ hM_in_spec; rwa [RCLike.ofReal_re] at this
        have hm_ge_zero : (0 : ℝ) ≤ m := by
          apply le_ciInf; intro x
          by_cases hx : x = 0
          · rw [hx, ContinuousLinearMap.rayleighQuotient_apply_zero]
          · have hSrq : S.rayleighQuotient x = M - T.rayleighQuotient x := hS_rq x hx
            have hSrq_zero : S.rayleighQuotient x = 0 := by
              rw [show S = 0 from hS_zero]
              exact ContinuousLinearMap.rayleighQuotient_zero_apply x
            linarith
        linarith
      have hS_spec_nonneg : ∀ ν ∈ spectrum 𝕜 S, 0 ≤ RCLike.re ν :=
        spectrum_re_nonneg_of_reApplyInnerSelf_nonneg hS_pos
      have hS_neg_not_mem : (↑(-‖S‖) : 𝕜) ∉ spectrum 𝕜 S := by
        intro h_mem
        have := hS_spec_nonneg _ h_mem
        rw [RCLike.ofReal_re] at this; linarith [norm_pos_iff.mpr hS_ne]
      have hS_norm_mem : (↑‖S‖ : 𝕜) ∈ spectrum 𝕜 S := by
        have h_or : (algebraMap ℝ 𝕜 ‖S‖) ∈ spectrum 𝕜 S ∨
            (algebraMap ℝ 𝕜 (-‖S‖)) ∈ spectrum 𝕜 S := by
          by_contra hcon
          rw [not_or] at hcon
          have h1 : (algebraMap ℝ 𝕜) ‖S‖ ∈ resolventSet 𝕜 S :=
            spectrum.mem_resolventSet_iff.mpr (spectrum.notMem_iff.mp hcon.1)
          have h2 : -(algebraMap ℝ 𝕜) ‖S‖ ∈ resolventSet 𝕜 S := by
            rw [← map_neg]
            exact spectrum.mem_resolventSet_iff.mpr (spectrum.notMem_iff.mp hcon.2)
          obtain ⟨c, hc0, hc⟩ := S.abs_rayleighQuotient_le_of_norm_mem_resolventSet h1 h2
          linarith [S.norm_eq_iSup_rayleighQuotient hS_sym, ciSup_le hc]
        rcases h_or with h1 | h2
        · convert h1 using 1
        · exfalso; apply hS_neg_not_mem; convert h2 using 1
      have hM_sub_norm_mem : (↑(M - ‖S‖) : 𝕜) ∈ spectrum 𝕜 T := by
        have h_in_S := hS_norm_mem
        rw [← spectrum.singleton_sub_eq] at h_in_S
        obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.mp h_in_S
        rw [Set.mem_singleton_iff] at ha; subst ha
        convert hb using 1
        have heq : (↑M : 𝕜) - b = (↑‖S‖ : 𝕜) := hab
        have hre := congr_arg RCLike.re heq
        have him := congr_arg RCLike.im heq
        simp only [map_sub, RCLike.ofReal_re, RCLike.ofReal_im] at hre him
        exact RCLike.ext (by simp only [RCLike.ofReal_re]; linarith)
          (by simp only [RCLike.ofReal_im]; linarith)
      have hS_le_M : ‖S‖ ≤ M := by
        have := hspec _ hM_sub_norm_mem; rw [RCLike.ofReal_re] at this; linarith
      have hS_gt_M : M < ‖S‖ := by
        rw [S.norm_eq_iSup_rayleighQuotient hS_sym]
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : H, T.rayleighQuotient x₀ < 0 := by
          by_contra h_all
          rw [not_exists] at h_all
          have hm_ge : (0 : ℝ) ≤ m := le_ciInf (fun x => le_of_not_gt (h_all x))
          linarith
        have hx₀_ne : x₀ ≠ 0 := by
          intro h; rw [h, ContinuousLinearMap.rayleighQuotient_apply_zero] at hx₀; linarith
        have hS_rq_x₀ : S.rayleighQuotient x₀ = M - T.rayleighQuotient x₀ := hS_rq x₀ hx₀_ne
        have hS_rq_gt : M < |S.rayleighQuotient x₀| := by
          rw [hS_rq_x₀, abs_of_nonneg (by linarith [hle_M x₀])]; linarith
        exact lt_of_lt_of_le hS_rq_gt
          (le_ciSup ⟨‖S‖, by rintro _ ⟨x, rfl⟩; exact S.rayleighQuotient_le_norm x⟩ x₀)
      linarith

end MathlibExt.Analysis.InnerProductSpace.SelfAdjointPositiveSpectrum
