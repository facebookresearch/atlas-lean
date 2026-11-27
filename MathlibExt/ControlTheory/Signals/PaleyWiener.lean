/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Compact-spectrum representative

For a real number `B` and a frequency profile `g`, `PW.rep B g` is the
inverse Fourier integral of `g` over the oriented interval from `-B` to
`B`: `PW.rep B g t = ∫ ν in (-B)..B, g ν * e^{2πiνt}`. For `0 ≤ B` this is
the integral over the symmetric band `[-B, B]`; negating `B` negates the
value, as for any oriented interval integral. It is a pointwise
representative, not an identification with an `L²` class.

If `g` is square integrable on the whole line, the representative is
continuous in `t`, additive and scalar-homogeneous in `g`, and Cauchy-Schwarz
on the band of length `2B` gives the pointwise bound
`‖PW.rep B g t‖ ≤ √(2B) * ‖g‖₂`. The support hypothesis one might expect is
not needed: the band norm is bounded by the whole-line norm, so the bound in
particular covers profiles vanishing almost everywhere off `[-B, B]`.

`PW.bandExt B g` is the zero extension of `g` from the band. For
`0 < B` and `0 < T` with `2 * B * T ≤ 1`, its one-period Fourier
coefficients at period `1 / T` are the samples `T * PW.rep B g (-n * T)`.
-/

open MeasureTheory intervalIntegral

@[expose] public section

namespace ControlTheory

namespace PW

/-- The compact-spectrum inverse-integral representative: for a real `B` and
a frequency profile `g : ℝ → ℂ`,
`PW.rep B g t = ∫ ν in (-B)..B, g ν * e^{2πi ν t}`, the inverse Fourier
integral of `g` over the oriented interval from `-B` to `B` (the symmetric
band `[-B, B]` when `0 ≤ B`). It is defined for every raw function `g`;
the theorems below impose an `L²` hypothesis, and the pointwise bound
also assumes `0 < B`. It is a pointwise representative, not an
identification with an `L²` class. -/
noncomputable def rep (B : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ν in (-B)..B, g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)

/-- The zero extension of a band profile: `PW.bandExt B g` agrees with `g`
on `[-B, B]` and is zero elsewhere. For `0 < B` and `0 < T` with
`B ≤ 1 / (2 * T)`, its one-period Fourier coefficients at period `1 / T`
are the samples of the representative `PW.rep`. -/
noncomputable def bandExt (B : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  (Set.Icc (-B) B).indicator g

private theorem norm_exp_factor (ν t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ν * t)‖ = 1 := by
  have h : (2 * Real.pi * Complex.I * ν * t : ℂ)
      = ((2 * Real.pi * ν * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem continuous_exp_factor_t (ν : ℝ) :
    Continuous (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ν * t)) := by
  continuity

private theorem continuous_exp_factor_ν (t : ℝ) :
    Continuous (fun ν : ℝ => Complex.exp (2 * Real.pi * Complex.I * ν * t)) := by
  continuity

private theorem integrable_norm_restrict {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (a b : ℝ) :
    Integrable (fun ν => ‖g ν‖) (volume.restrict (Set.Ioc a b)) := by
  have hfin := Real.isFiniteMeasure_restrict_Ioc a b
  have h1 : MemLp (fun ν => ‖g ν‖) 2 (volume.restrict (Set.Ioc a b)) :=
    MemLp.restrict (Set.Ioc a b) hg.norm
  exact MemLp.integrable one_le_two h1

private theorem continuous_param_integral {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (a b : ℝ) :
    Continuous (fun t : ℝ => ∫ ν, g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)
      ∂(volume.restrict (Set.Ioc a b))) := by
  refine continuous_of_dominated (bound := fun ν => ‖g ν‖) ?_ ?_ ?_ ?_
  · intro t
    exact AEStronglyMeasurable.mul hg.aestronglyMeasurable.restrict
      (continuous_exp_factor_ν t).aestronglyMeasurable
  · intro t
    filter_upwards with ν
    simp [norm_exp_factor ν t]
  · exact integrable_norm_restrict hg a b
  · filter_upwards with ν
    exact Continuous.mul continuous_const (continuous_exp_factor_t ν)

/-- Additivity of `PW.rep` in the frequency profile on the band, for
profiles whose band integrands are interval integrable. -/
theorem rep_add {B : ℝ} {g h : ℝ → ℂ}
    (hg : IntervalIntegrable g volume (-B) B)
    (hh : IntervalIntegrable h volume (-B) B) (t : ℝ) :
    rep B (g + h) t = rep B g t + rep B h t := by
  have hE : ContinuousOn
      (fun ν : ℝ => Complex.exp (2 * Real.pi * Complex.I * ν * t)) (Set.uIcc (-B) B) :=
    (continuous_exp_factor_ν t).continuousOn
  have hg' : IntervalIntegrable
      (fun ν => g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)) volume (-B) B :=
    hg.mul_continuousOn hE
  have hh' : IntervalIntegrable
      (fun ν => h ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)) volume (-B) B :=
    hh.mul_continuousOn hE
  simp only [rep, Pi.add_apply, add_mul]
  exact intervalIntegral.integral_add hg' hh'

/-- Scalar homogeneity of `PW.rep` in the frequency profile. -/
theorem rep_smul {B : ℝ} {c : ℂ} {g : ℝ → ℂ} (t : ℝ) :
    rep B (c • g) t = c * rep B g t := by
  show ∫ ν in (-B)..B, (c • g) ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)
    = c * ∫ ν in (-B)..B, g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)
  have hfun : (fun ν => (c • g) ν * Complex.exp (2 * Real.pi * Complex.I * ν * t))
      = fun ν => c * (g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)) := by
    funext ν
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [hfun]
  exact intervalIntegral.integral_const_mul c _

/-- Continuity of the compact-spectrum representative: if the frequency
profile `g` is square integrable on the whole line, then `t ↦ PW.rep B g t`
is continuous. Square integrability on the line restricts to integrability
on the finite band, and continuity follows by dominated convergence. -/
theorem rep_continuous {B : ℝ} {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    Continuous (rep B g) := by
  by_cases hle : -B ≤ B
  · have heq : rep B g = fun t : ℝ =>
        ∫ ν, g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)
          ∂(volume.restrict (Set.Ioc (-B) B)) := by
      funext t
      exact integral_of_le hle
    rw [heq]
    exact continuous_param_integral hg (-B) B
  · have hle' : B ≤ -B := le_of_lt (lt_of_not_ge hle)
    have heq : rep B g = fun t : ℝ =>
        -∫ ν, g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)
          ∂(volume.restrict (Set.Ioc B (-B))) := by
      funext t
      rw [show rep B g t
          = ∫ ν in (-B)..B, g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t) from rfl,
        integral_symm B (-B), integral_of_le hle']
    rw [heq]
    exact (continuous_param_integral hg B (-B)).neg

/-- Pointwise bound on the compact-spectrum representative: for `0 < B`, a
square-integrable frequency profile `g`, and every time `t`,
`‖PW.rep B g t‖ ≤ √(2B) * ‖g‖₂`, where `‖g‖₂` is
`(eLpNorm g 2 volume).toReal`. This is Cauchy-Schwarz on the band of
length `2B`. No support hypothesis is needed: the band norm is bounded by
the whole-line norm. In particular the bound holds when `g` vanishes
almost everywhere off `[-B, B]`. -/
theorem norm_rep_le {B : ℝ} {g : ℝ → ℂ} (hB : 0 < B) (hg : MemLp g 2 volume)
    (t : ℝ) :
    ‖rep B g t‖ ≤ Real.sqrt (2 * B) * (eLpNorm g 2 volume).toReal := by
  have hle : -B ≤ B := by linarith
  have hfin := Real.isFiniteMeasure_restrict_Ioc (-B) B
  have h1 : MemLp (fun ν => ‖g ν‖) 2 (volume.restrict (Set.Ioc (-B) B)) :=
    MemLp.restrict (Set.Ioc (-B) B) hg.norm
  have h2 : MemLp (fun _ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc (-B) B)) := memLp_const 1
  have hInt : Integrable (fun ν => ‖g ν‖) (volume.restrict (Set.Ioc (-B) B)) :=
    MemLp.integrable one_le_two h1
  show ‖∫ ν in (-B)..B, g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)‖
    ≤ Real.sqrt (2 * B) * (eLpNorm g 2 volume).toReal
  rw [integral_of_le hle]
  have hbound : ∀ᵐ ν ∂(volume.restrict (Set.Ioc (-B) B)),
      ‖g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)‖ ≤ ‖g ν‖ := by
    filter_upwards with ν
    simp [norm_exp_factor ν t]
  have hstep1 : ‖∫ ν, g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t)
      ∂(volume.restrict (Set.Ioc (-B) B))‖
      ≤ ∫ ν, ‖g ν‖ ∂(volume.restrict (Set.Ioc (-B) B)) :=
    MeasureTheory.norm_integral_le_of_norm_le hInt hbound
  have hholder : eLpNorm (fun ν => ‖g ν‖ * 1) 1 (volume.restrict (Set.Ioc (-B) B))
      ≤ eLpNorm (fun ν => ‖g ν‖) 2 (volume.restrict (Set.Ioc (-B) B))
        * eLpNorm (fun _ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc (-B) B)) := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (μ := volume.restrict (Set.Ioc (-B) B))
      (f := fun ν => ‖g ν‖) (g := fun _ => (1 : ℝ)) (p := 2) (q := 2) (r := 1)
      (fun x1 x2 : ℝ => x1 * x2) 1 ?hcont ?hae1 ?hae2 ?hbnd
    · simpa using h
    · exact Continuous.mul continuous_fst continuous_snd
    · exact h1.aestronglyMeasurable
    · exact aestronglyMeasurable_const
    · filter_upwards with ν
      simp
  have hLp1 : (eLpNorm (fun ν => ‖g ν‖ * 1) 1 (volume.restrict (Set.Ioc (-B) B))).toReal
      = ∫ ν, ‖g ν‖ * 1 ∂(volume.restrict (Set.Ioc (-B) B)) := by
    have hInt1 : Integrable (fun ν => ‖g ν‖ * 1)
        (volume.restrict (Set.Ioc (-B) B)) := by
      have h3 := h1.integrable_mul h2
      have hfun : (fun ν => ‖g ν‖) * (fun _ => (1 : ℝ)) = fun ν => ‖g ν‖ * 1 := by
        funext ν
        simp [Pi.mul_apply]
      rw [hfun] at h3
      exact h3
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (-B) B)] fun ν => ‖g ν‖ * 1 := by
      filter_upwards with ν
      positivity
    have hae : AEStronglyMeasurable (fun ν => ‖g ν‖ * 1)
        (volume.restrict (Set.Ioc (-B) B)) := hInt1.aestronglyMeasurable
    have h1e := eLpNorm_one_eq_lintegral_enorm hae
    have h2e := ofReal_integral_eq_lintegral_ofReal hInt1 hnonneg
    have h3e : (∫⁻ ν, ‖‖g ν‖ * 1‖ₑ ∂(volume.restrict (Set.Ioc (-B) B)))
        = ∫⁻ ν, ENNReal.ofReal (‖g ν‖ * 1) ∂(volume.restrict (Set.Ioc (-B) B)) := by
      apply lintegral_congr_ae
      filter_upwards with ν
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity)]
    rw [h1e, h3e, ← h2e, ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg_of_ae hnonneg)]
  have hfin1 : eLpNorm (fun ν => ‖g ν‖) 2 (volume.restrict (Set.Ioc (-B) B)) ≠ ⊤ :=
    ne_of_lt h1.eLpNorm_lt_top
  have hfin2 : eLpNorm (fun _ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc (-B) B)) ≠ ⊤ :=
    ne_of_lt h2.eLpNorm_lt_top
  have htoReal := ENNReal.toReal_mono (ENNReal.mul_ne_top hfin1 hfin2) hholder
  rw [ENNReal.toReal_mul, hLp1] at htoReal
  have hA : (eLpNorm (fun ν => ‖g ν‖) 2 (volume.restrict (Set.Ioc (-B) B))).toReal
      ≤ (eLpNorm g 2 volume).toReal := by
    have hnorm : eLpNorm (fun ν => ‖g ν‖) 2 (volume.restrict (Set.Ioc (-B) B))
        = eLpNorm g 2 (volume.restrict (Set.Ioc (-B) B)) :=
      eLpNorm_norm g hg.aestronglyMeasurable.restrict
    rw [hnorm]
    exact ENNReal.toReal_mono hg.eLpNorm_lt_top.ne (eLpNorm_restrict_le g 2 volume _)
  have hB2 : (eLpNorm (fun _ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc (-B) B))).toReal
      = Real.sqrt (2 * B) := by
    have h2B : (0 : ℝ) ≤ 2 * B := by linarith
    have hμ : volume.restrict (Set.Ioc (-B) B) ≠ 0 := by
      intro hcon
      have hh1 : (volume.restrict (Set.Ioc (-B) B)) Set.univ
          = volume (Set.Ioc (-B) B) :=
        Measure.restrict_apply_univ _
      rw [hcon] at hh1
      have hvol : volume (Set.Ioc (-B) B) = 0 := by simpa using hh1.symm
      rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hvol
      linarith
    have h2r : (2 : ENNReal).toReal = 2 := by norm_num
    have hconst := eLpNorm_const (μ := volume.restrict (Set.Ioc (-B) B)) (p := 2) (1 : ℝ)
      (by simp) hμ
    have hsub : B - -B = 2 * B := by ring
    rw [hconst, ENNReal.toReal_mul, enorm_one, ENNReal.toReal_one, one_mul,
      Measure.restrict_apply_univ, Real.volume_Ioc, hsub, h2r, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal h2B]
    exact (Real.sqrt_eq_rpow _).symm
  have hmul : (∫ ν, ‖g ν‖ ∂(volume.restrict (Set.Ioc (-B) B)))
      = ∫ ν, ‖g ν‖ * 1 ∂(volume.restrict (Set.Ioc (-B) B)) := by simp
  have hfinal : (∫ ν, ‖g ν‖ ∂(volume.restrict (Set.Ioc (-B) B)))
      ≤ Real.sqrt (2 * B) * (eLpNorm g 2 volume).toReal := by
    rw [hmul]
    calc ∫ ν, ‖g ν‖ * 1 ∂(volume.restrict (Set.Ioc (-B) B))
        ≤ (eLpNorm (fun ν => ‖g ν‖) 2 (volume.restrict (Set.Ioc (-B) B))).toReal
          * (eLpNorm (fun _ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc (-B) B))).toReal :=
          htoReal
      _ ≤ (eLpNorm g 2 volume).toReal
          * (eLpNorm (fun _ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc (-B) B))).toReal :=
          mul_le_mul_of_nonneg_right hA ENNReal.toReal_nonneg
      _ = Real.sqrt (2 * B) * (eLpNorm g 2 volume).toReal := by
          rw [hB2]
          exact mul_comm _ _
  exact hstep1.trans hfinal

private theorem ae_compl_Ioc_eq_zero {B a b : ℝ} {F : ℝ → ℂ}
    (hF : ∀ x, x ∉ Set.Icc (-B) B → F x = 0)
    (haB : a ≤ -B) (hBb : B ≤ b) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc a b → F x = 0 := by
  have hsing : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ -B := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬x ≠ -B} = {-B} := by
      ext x
      simp
    rw [hset]
    exact Real.volume_singleton
  filter_upwards [hsing] with x hx hmem
  apply hF
  intro hcon
  rw [Set.mem_Icc] at hcon
  obtain ⟨hxlo, hxhi⟩ := hcon
  simp only [Set.mem_Ioc, not_and] at hmem
  by_cases h : a < x
  · exact hmem h (le_trans hxhi hBb)
  · have hle' : x ≤ a := not_lt.mp h
    exact hx (le_antisymm (le_trans hle' haB) hxlo)

private theorem integral_window_eq_integral_band {B : ℝ} {E : ℝ → ℂ} {g : ℝ → ℂ}
    {a b : ℝ} (hab : a ≤ b) (hBB : -B ≤ B) (haB : a ≤ -B) (hBb : B ≤ b) :
    ∫ x in a..b, E x • bandExt B g x = ∫ x in (-B)..B, E x • bandExt B g x := by
  have hF : ∀ x, x ∉ Set.Icc (-B) B → E x • bandExt B g x = 0 := by
    intro x hx
    unfold bandExt
    rw [Set.indicator_of_notMem hx]
    exact smul_zero _
  rw [integral_of_le hab, integral_of_le hBB,
    setIntegral_eq_integral_of_ae_compl_eq_zero (ae_compl_Ioc_eq_zero hF haB hBb),
    setIntegral_eq_integral_of_ae_compl_eq_zero (ae_compl_Ioc_eq_zero hF le_rfl le_rfl)]

/-- Sample-coefficient identity: for `0 < B`, `0 < T` with `2 * B * T ≤ 1`,
and a profile `g` integrable on the band `[-B, B]`, the `n`-th Fourier
coefficient of the zero extension of `g` over one period `1 / T` (window
`[-1 / (2 * T), 1 / (2 * T)]`) is `T` times the representative at the
sample `-n * T`:
`fourierCoeffOn (bandExt B g) n = T * PW.rep B g (-n * T)`.
The index sign is the one forced by the `+2πi` inverse convention of
`PW.rep` and the `fourier (-n)` convention of `fourierCoeffOn`. -/
theorem fourierCoeff_eq_sample {B T : ℝ} (hB : 0 < B) (hT : 0 < T)
    (hle : 2 * B * T ≤ 1) {g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume (-B) B) (n : ℤ) :
    fourierCoeffOn (show (-(1 / (2 * T)) : ℝ) < 1 / (2 * T) by
      rw [neg_lt_self_iff]
      positivity) (bandExt B g) n
      = (T : ℂ) * rep B g (-(n : ℝ) * T) := by
  have _ := hg
  have hT' : T ≠ 0 := ne_of_gt hT
  have h2T : (2:ℝ) * T ≠ 0 := mul_ne_zero (by norm_num) hT'
  have hba : 1 / (2 * T) - -(1 / (2 * T)) = 1 / T := by
    field_simp
    ring
  have h2Tpos : (0:ℝ) < 2 * T := by positivity
  have hBle : B ≤ 1 / (2 * T) := by
    rw [le_div_iff₀ h2Tpos]
    have hmul : B * (2 * T) = 2 * B * T := by ring
    rw [hmul]
    exact hle
  have hab' : -(1 / (2 * T)) ≤ 1 / (2 * T) :=
    neg_le_self_iff.mpr (le_of_lt (by positivity : (0:ℝ) < 1 / (2 * T)))
  have hBB : -B ≤ B := neg_le_self_iff.mpr (le_of_lt hB)
  have haB : -(1 / (2 * T)) ≤ -B := neg_le_neg_iff.mpr hBle
  rw [fourierCoeffOn_eq_integral, hba, one_div_one_div, Complex.real_smul]
  unfold rep
  congr 1
  rw [integral_window_eq_integral_band hab' hBB haB hBle]
  apply integral_congr
  rw [Set.uIcc_of_le hBB]
  intro x hx
  dsimp only
  unfold bandExt
  rw [Set.indicator_of_mem hx g, smul_eq_mul, fourier_coe_apply,
    mul_comm (Complex.exp _) (g x)]
  congr 1
  push_cast
  have hTc : (T:ℂ) ≠ 0 := by exact_mod_cast hT'
  field_simp

end PW

end ControlTheory
