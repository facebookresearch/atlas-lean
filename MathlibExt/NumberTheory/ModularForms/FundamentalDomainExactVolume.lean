/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_FundamentalDomainExactVolume.lean`
and
`Definitions/Def_AutomorphicForm_FundamentalDomainVolume.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.NumberTheory.Modular

@[expose] public section

open MeasureTheory Set ModularGroup UpperHalfPlane
open scoped MatrixGroups Modular Pointwise NNReal ENNReal

noncomputable section

private lemma density_eq_ofReal_rpow {y : ℝ} (hy : 0 < y) :
    (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (y ^ (-2 : ℝ)) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [Real.norm_eq_abs, abs_of_pos hy,
    show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy.le, Real.rpow_natCast,
    one_div, inv_pow]

namespace UpperHalfPlane

/-- The density `1 / y ^ 2` of the hyperbolic measure `dx dy / y ^ 2` integrates to `1 / c`
over the vertical ray `y ≥ c`, for `c > 0`. -/
public theorem setLIntegral_Ici_density {c : ℝ} (hc : 0 < c) :
    ∫⁻ y in Set.Ici c, (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal c⁻¹ := by
  rw [← MeasureTheory.setLIntegral_congr
    (MeasureTheory.Ioi_ae_eq_Ici' (measure_singleton c))]
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    (fun y (hy : y ∈ Set.Ioi c) => density_eq_ofReal_rpow (hc.trans hy))]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hc)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall
        (fun y hy => Real.rpow_nonneg (le_of_lt (hc.trans hy)) _)))]
  rw [integral_Ioi_rpow_of_lt (by norm_num) hc]
  norm_num [Real.rpow_neg_one]

end UpperHalfPlane

private lemma arcsin_one_half : Real.arcsin (1 / 2) = Real.pi / 6 := by
  rw [← Real.sin_pi_div_six]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

private lemma continuousOn_inv_sqrt :
    ContinuousOn (fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹)
      (Set.uIcc (-(1 / 2) : ℝ) (1 / 2)) := by
  apply ContinuousOn.inv₀
  · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
  · intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    have hx2 : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      apply sq_le_sq'
      · linarith [hx.1]
      · linarith [hx.2]
    have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
    exact ne_of_gt (Real.sqrt_pos.mpr hpos)

/-- The integral of `1 / √(1 - x ^ 2)` over `[-1/2, 1/2]` is `π / 3`: the antiderivative is
`arcsin`, and `arcsin (1 / 2) = π / 6`. -/
public theorem integral_inv_sqrt_one_sub_sq :
    ∫ x in (-(1 / 2) : ℝ)..(1 / 2), (Real.sqrt (1 - x ^ 2))⁻¹ = Real.pi / 3 := by
  have hderiv : ∀ x ∈ Set.uIcc (-(1 / 2) : ℝ) (1 / 2),
      HasDerivAt Real.arcsin (Real.sqrt (1 - x ^ 2))⁻¹ x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    have h₁ : x ≠ -1 := by intro h; rw [h] at hx; have := hx.1; norm_num at this
    have h₂ : x ≠ 1 := by intro h; rw [h] at hx; have := hx.2; norm_num at this
    simpa [one_div] using Real.hasDerivAt_arcsin h₁ h₂
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    continuousOn_inv_sqrt.intervalIntegrable]
  rw [Real.arcsin_neg, arcsin_one_half]
  ring

namespace ModularGroup

/-- The lower boundary of the standard fundamental domain, an arc of the unit circle, as the
graph of `x ↦ √(1 - x ^ 2)`. -/
public def lowerArc (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

@[simp]
public theorem lowerArc_zero : lowerArc 0 = 1 := by simp [lowerArc]

public theorem lowerArc_pos {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) :
    0 < lowerArc x := by
  have hx2 : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    apply sq_le_sq'
    · linarith [hx.1]
    · linarith [hx.2]
  have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  exact Real.sqrt_pos.mpr hpos

/-- The image of the standard fundamental domain in real coordinates:
points above the lower arc and between `-1/2` and `1/2`. -/
public def fundamentalRegion : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) ∧ lowerArc p.1 ≤ p.2}

public theorem mem_fundamentalRegion {p : ℝ × ℝ} :
    p ∈ fundamentalRegion ↔
      p.1 ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) ∧ lowerArc p.1 ≤ p.2 :=
  Iff.rfl

public theorem measurableSet_fundamentalRegion : MeasurableSet fundamentalRegion := by
  change MeasurableSet ({p : ℝ × ℝ | p.1 ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)} ∩
    {p : ℝ × ℝ | lowerArc p.1 ≤ p.2})
  apply MeasurableSet.inter
  · exact measurable_fst measurableSet_Icc
  · apply measurableSet_le _ measurable_snd
    have hcont : Continuous fun p : ℝ × ℝ => lowerArc p.1 := by
      unfold lowerArc
      fun_prop
    exact hcont.measurable

public theorem image_image_fd :
    Complex.measurableEquivRealProd '' (UpperHalfPlane.coe '' 𝒟) = fundamentalRegion := by
  ext p
  constructor
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨hnorm, hre⟩ := hz
    have him : (0 : ℝ) < z.im := z.im_pos
    have hxIcc : z.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
      rcases abs_le.mp hre with ⟨h₁, h₂⟩
      exact ⟨by linarith, h₂⟩
    refine ⟨?_, ?_⟩
    · simpa only [Complex.measurableEquivRealProd_apply, UpperHalfPlane.coe_re] using hxIcc
    · have hsq : 1 - z.re ^ 2 ≤ z.im ^ 2 := by
        rw [Complex.normSq_apply] at hnorm
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hnorm
        nlinarith
      simp only [Complex.measurableEquivRealProd_apply, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      calc lowerArc z.re ≤ Real.sqrt (z.im ^ 2) := Real.sqrt_le_sqrt hsq
        _ = z.im := by rw [Real.sqrt_sq him.le]
  · rintro ⟨hx, hy⟩
    have hypos : (0 : ℝ) < p.2 := lt_of_lt_of_le (lowerArc_pos hx) hy
    have h1x : (0 : ℝ) ≤ 1 - p.1 ^ 2 := by
      have hx2 : p.1 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        apply sq_le_sq'
        · linarith [hx.1]
        · linarith [hx.2]
      nlinarith
    have himC : (0 : ℝ) < (Complex.measurableEquivRealProd.symm p).im := by
      rw [Complex.measurableEquivRealProd_symm_apply]
      exact hypos
    refine ⟨Complex.measurableEquivRealProd.symm p,
      ⟨⟨Complex.measurableEquivRealProd.symm p, himC⟩, ⟨?_, ?_⟩, rfl⟩,
      Complex.measurableEquivRealProd.apply_symm_apply p⟩
    · rw [Complex.normSq_apply]
      change (1 : ℝ) ≤ (Complex.measurableEquivRealProd.symm p).re *
        (Complex.measurableEquivRealProd.symm p).re +
        (Complex.measurableEquivRealProd.symm p).im *
        (Complex.measurableEquivRealProd.symm p).im
      rw [Complex.measurableEquivRealProd_symm_apply]
      have hsq : 1 - p.1 ^ 2 ≤ p.2 ^ 2 := by
        calc 1 - p.1 ^ 2 = lowerArc p.1 ^ 2 := (Real.sq_sqrt h1x).symm
          _ ≤ p.2 ^ 2 := by
              apply pow_le_pow_left₀ (Real.sqrt_nonneg _) hy
      nlinarith
    · change |(⟨Complex.measurableEquivRealProd.symm p, himC⟩ : ℍ).re| ≤ (1 : ℝ) / 2
      have hthis : (⟨Complex.measurableEquivRealProd.symm p, himC⟩ : ℍ).re = p.1 := by
        change (Complex.measurableEquivRealProd.symm p).re = p.1
        rw [Complex.measurableEquivRealProd_symm_apply]
      rw [hthis]
      exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩

private def densityP (p : ℝ × ℝ) : ℝ≥0∞ := (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)

private lemma measurable_densityP : Measurable densityP := by
  unfold densityP
  fun_prop

private lemma inner_slice (x : ℝ) :
    ∫⁻ y, fundamentalRegion.indicator densityP (x, y) =
      Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2))
        (fun x' => ENNReal.ofReal (lowerArc x')⁻¹) x := by
  by_cases hx : x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
  · rw [Set.indicator_of_mem hx]
    have hslice : (fun y => fundamentalRegion.indicator densityP (x, y)) =
        (Set.Ici (lowerArc x)).indicator
          (fun y => (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) := by
      funext y
      by_cases hy : lowerArc x ≤ y
      · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy),
          Set.indicator_of_mem (show (x, y) ∈ fundamentalRegion from ⟨hx, hy⟩)]
        rfl
      · rw [Set.indicator_of_notMem (fun h => hy (Set.mem_Ici.mp h)),
          Set.indicator_of_notMem (fun (h : (x, y) ∈ fundamentalRegion) => hy h.2)]
    rw [hslice, lintegral_indicator measurableSet_Ici]
    exact setLIntegral_Ici_density (lowerArc_pos hx)
  · rw [Set.indicator_of_notMem hx]
    have hzero : (fun y => fundamentalRegion.indicator densityP (x, y)) = fun _ => 0 := by
      funext y
      exact Set.indicator_of_notMem (fun (h : (x, y) ∈ fundamentalRegion) => hx h.1) _
    rw [hzero, lintegral_zero]

/-- The hyperbolic volume of the standard modular fundamental domain `𝒟` is `π / 3`, where the
upper half-plane carries the invariant measure `dx dy / y ^ 2`. -/
public theorem volume_fd_eq : volume 𝒟 = ENNReal.ofReal (Real.pi / 3) := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  have hfactor : ∀ z : ℂ, (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) =
      densityP (Complex.measurableEquivRealProd z) := fun z => rfl
  simp only [hfactor]
  rw [Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding densityP _]
  rw [image_image_fd]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl]
  rw [← lintegral_indicator measurableSet_fundamentalRegion]
  rw [MeasureTheory.lintegral_prod _
    ((measurable_densityP.indicator measurableSet_fundamentalRegion).aemeasurable)]
  simp only [inner_slice]
  rw [lintegral_indicator measurableSet_Icc]
  have hcont : ContinuousOn (fun x : ℝ => (lowerArc x)⁻¹)
      (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    have h := continuousOn_inv_sqrt
    rwa [Set.uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at h
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hcont.integrableOn_compact isCompact_Icc)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall
        (fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg _))))]
  congr 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
  exact integral_inv_sqrt_one_sub_sq

public theorem volume_fd_toReal : (volume 𝒟).toReal = Real.pi / 3 := by
  rw [volume_fd_eq, ENNReal.toReal_ofReal (by positivity)]

public theorem volume_fd_lt_top : volume 𝒟 < ⊤ := by
  rw [volume_fd_eq]; exact ENNReal.ofReal_lt_top

public theorem volume_fd_ne_zero : volume 𝒟 ≠ 0 := by
  rw [volume_fd_eq]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

public theorem residue_mul_volume_fd :
    (3 / (Real.pi : ℂ)) * ((volume 𝒟).toReal : ℂ) = 1 := by
  rw [volume_fd_toReal]
  push_cast
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

public theorem volume_fd_toReal_eq :
    ((volume 𝒟).toReal : ℂ) = (Real.pi : ℂ) / 3 := by
  rw [volume_fd_toReal]; push_cast; ring

end ModularGroup
