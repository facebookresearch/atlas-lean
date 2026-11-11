/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import MathlibExt.Probability.Distributions.ChiSquare

/-!
# Student's `t` law

`studentTMeasure k` is Student's `t` law with `k` degrees of freedom, defined by its density
`Γ((k + 1)/2) / (√(k π) Γ(k/2)) · (1 + t²/k)^{-(k+1)/2}` with respect to Lebesgue measure.
We prove it is a probability measure for `k ≥ 1`.

The normalization uses gamma mixing rather than the beta function: for `c ≥ 0`,
`(1 + c)^{-s} = ∫ γ_{s,1}(y) e^{-c y} dy`, and after Tonelli the inner integral in `t` is
Gaussian, leaving the gamma moment `E[Y^{-1/2}] = Γ(s - 1/2) / Γ(s)`.

We also prove the ratio law: for independent `Z ~ N(0, 1)` and `V ~ χ²_k`, `Z / √(V / k)` has
law `studentTMeasure k`. For fixed `v > 0` the substitution `z = √(v/k) t` turns the Gaussian
integral into one over `t`; after Tonelli the integral over `v` is a gamma normalization.

## Main results

* `ProbabilityTheory.lintegral_gammaPDF_mul_exp`: `∫ γ_{a,r}(y) e^{-c y} dy = (r / (r + c))^a`.
* `ProbabilityTheory.lintegral_gammaPDF_mul_rpow`: `∫ γ_{a,r}(y) y^b dy = Γ(a + b) / (Γ(a) r^b)`.
* `ProbabilityTheory.lintegral_one_add_sq_div_rpow_neg`:
  `∫ (1 + t²/c)^{-s} dt = √(c π) Γ(s - 1/2) / Γ(s)`.
* `ProbabilityTheory.isProbabilityMeasure_studentTMeasure`.
* `ProbabilityTheory.map_div_sqrt_chiSquare_eq_studentT`: `Z / √(V / k) ~ t_k`.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002),
  Definition 5.3.4.
-/

open MeasureTheory Set Real

open scoped ENNReal

namespace ProbabilityTheory

@[expose] public section

noncomputable section

/-! ### Gamma mixing identities -/

/-- Exponential tilting of the gamma density: `γ_{a,r}(y) e^{-c y} = (r/(r+c))^a γ_{a,r+c}(y)`. -/
lemma gammaPDFReal_mul_exp {a r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) (y : ℝ) :
    gammaPDFReal a r y * exp (-(c * y)) = (r / (r + c)) ^ a * gammaPDFReal a (r + c) y := by
  unfold gammaPDFReal
  split_ifs with hy
  · rw [div_rpow hr.le (by positivity)]
    have hrc : (r + c) ^ a ≠ 0 := (rpow_pos_of_pos (by positivity) a).ne'
    have hexp : exp (-((r + c) * y)) = exp (-(r * y)) * exp (-(c * y)) := by
      rw [← exp_add]; ring_nf
    rw [hexp]
    field_simp
  · simp

/-- Laplace transform of the gamma density, as a lower Lebesgue integral. -/
theorem lintegral_gammaPDF_mul_exp {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : 0 ≤ c) :
    ∫⁻ y, gammaPDF a r y * ENNReal.ofReal (exp (-(c * y))) =
      ENNReal.ofReal ((r / (r + c)) ^ a) := by
  have hrc : 0 < r + c := by positivity
  simp_rw [gammaPDF, ← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hr _),
    gammaPDFReal_mul_exp hr hc, ENNReal.ofReal_mul (by positivity : 0 ≤ (r / (r + c)) ^ a)]
  rw [lintegral_const_mul _ (measurable_gammaPDFReal a (r + c)).ennreal_ofReal]
  rw [show (∫⁻ x, ENNReal.ofReal (gammaPDFReal a (r + c) x)) = 1 from
    lintegral_gammaPDF_eq_one ha hrc, mul_one]

/-- Real-power moments of the gamma density, pointwise off `0`. -/
lemma gammaPDFReal_mul_rpow {a b r y : ℝ} (hab : 0 < a + b) (hr : 0 < r) (hy : y ≠ 0) :
    gammaPDFReal a r y * y ^ b =
      Gamma (a + b) / (Gamma a * r ^ b) * gammaPDFReal (a + b) r y := by
  unfold gammaPDFReal
  split_ifs with h0
  · have hy0 : 0 < y := lt_of_le_of_ne h0 (Ne.symm hy)
    have hG : Gamma (a + b) ≠ 0 := (Gamma_pos_of_pos hab).ne'
    have hrb : r ^ b ≠ 0 := (rpow_pos_of_pos hr b).ne'
    rw [rpow_add hr, show a + b - 1 = (a - 1) + b by ring, rpow_add hy0]
    field_simp
  · simp

/-- Real-power moments of the gamma law: `∫ γ_{a,r}(y) y^b dy = Γ(a + b) / (Γ(a) r^b)` for
`a + b > 0`. -/
theorem lintegral_gammaPDF_mul_rpow {a b r : ℝ} (ha : 0 < a) (hab : 0 < a + b) (hr : 0 < r) :
    ∫⁻ y, gammaPDF a r y * ENNReal.ofReal (y ^ b) =
      ENNReal.ofReal (Gamma (a + b) / (Gamma a * r ^ b)) := by
  have hC : 0 ≤ Gamma (a + b) / (Gamma a * r ^ b) := by
    have := Gamma_pos_of_pos hab; have := Gamma_pos_of_pos ha
    have := rpow_pos_of_pos hr b; positivity
  have hae : (fun y => gammaPDF a r y * ENNReal.ofReal (y ^ b)) =ᵐ[volume]
      fun y => ENNReal.ofReal (Gamma (a + b) / (Gamma a * r ^ b)) * gammaPDF (a + b) r y := by
    filter_upwards [Measure.ae_ne volume 0] with y hy
    rcases lt_or_gt_of_ne hy with hy' | hy'
    · simp [gammaPDF_of_neg hy']
    · rw [gammaPDF, gammaPDF, ← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hr _),
        gammaPDFReal_mul_rpow hab hr hy, ENNReal.ofReal_mul hC]
  rw [lintegral_congr_ae hae, lintegral_const_mul _ (measurable_gammaPDF _ _),
    lintegral_gammaPDF_eq_one hab hr, mul_one]

/-- The Gaussian integral as a lower Lebesgue integral. -/
lemma lintegral_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫⁻ x : ℝ, ENNReal.ofReal (exp (-b * x ^ 2)) = ENNReal.ofReal (√(π / b)) := by
  rw [← integral_gaussian, ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq hb)
    (ae_of_all _ fun _ => (exp_pos _).le)]

/-- The Student `t` normalizing integral:
`∫ (1 + t²/c)^{-s} dt = √(c π) Γ(s - 1/2) / Γ(s)` for `c > 0`, `s > 1/2`. -/
theorem lintegral_one_add_sq_div_rpow_neg {c s : ℝ} (hc : 0 < c) (hs : 1 / 2 < s) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2 / c) ^ (-s)) =
      ENNReal.ofReal (√(c * π) * Gamma (s - 1 / 2) / Gamma s) := by
  have hs0 : 0 < s := by linarith
  have h1 : ∀ t : ℝ, ENNReal.ofReal ((1 + t ^ 2 / c) ^ (-s)) =
      ∫⁻ y, gammaPDF s 1 y * ENNReal.ofReal (exp (-((t ^ 2 / c) * y))) := by
    intro t
    have hpos : 0 < 1 + t ^ 2 / c := by positivity
    rw [lintegral_gammaPDF_mul_exp hs0 one_pos (by positivity), rpow_neg hpos.le, one_div,
      inv_rpow hpos.le]
  simp_rw [h1]
  have hmeas : Measurable (Function.uncurry fun (t y : ℝ) =>
      gammaPDF s 1 y * ENNReal.ofReal (exp (-((t ^ 2 / c) * y)))) :=
    ((measurable_gammaPDF s 1).comp measurable_snd).mul (by fun_prop)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h2 : ∀ᵐ y ∂(volume : Measure ℝ),
      ∫⁻ t : ℝ, gammaPDF s 1 y * ENNReal.ofReal (exp (-((t ^ 2 / c) * y))) =
        ENNReal.ofReal √(c * π) * (gammaPDF s 1 y * ENNReal.ofReal (y ^ (-(1 / 2 : ℝ)))) := by
    filter_upwards [Measure.ae_ne volume 0] with y hy
    rcases lt_or_gt_of_ne hy with hy' | hy'
    · simp [gammaPDF_of_neg hy']
    · rw [lintegral_const_mul' _ _ (by simp [gammaPDF])]
      have hfun : (fun t : ℝ => ENNReal.ofReal (exp (-((t ^ 2 / c) * y)))) =
          fun t => ENNReal.ofReal (exp (-(y / c) * t ^ 2)) := by
        funext t; congr 2; ring
      have hsq : √(π / (y / c)) = √(c * π) * y ^ (-(1 / 2 : ℝ)) := by
        rw [show π / (y / c) = c * π / y by field_simp, sqrt_div (by positivity),
          rpow_neg hy'.le, ← sqrt_eq_rpow, div_eq_mul_inv]
      rw [hfun, lintegral_exp_neg_mul_sq (by positivity), hsq,
        ENNReal.ofReal_mul (sqrt_nonneg _)]
      ring
  rw [lintegral_congr_ae h2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_gammaPDF_mul_rpow hs0 (by linarith) one_pos,
    ← ENNReal.ofReal_mul (sqrt_nonneg _)]
  congr 1
  rw [one_rpow, mul_one, show s + -(1 / 2) = s - 1 / 2 by ring]
  ring

/-! ### Student's `t` law -/

/-- **Student's `t` law** with `k` degrees of freedom (Casella–Berger, Definition 5.3.4): the
measure with Lebesgue density `Γ((k + 1)/2) / (√(k π) Γ(k/2)) · (1 + t²/k)^{-(k+1)/2}`.
The density is copied verbatim from
`ProbabilityTheory.NormalTheoryWanted.map_div_sqrt_chiSquare_eq_studentT`. It is a probability
measure for `k ≥ 1` (`isProbabilityMeasure_studentTMeasure`); for `k = 0` it is the zero
measure. -/
noncomputable def studentTMeasure (k : ℕ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal
    (Gamma ((k + 1) / 2) / (√(k * π) * Gamma (k / 2)) *
      (1 + t ^ 2 / k) ^ (-((k : ℝ) + 1) / 2))

theorem isProbabilityMeasure_studentTMeasure {k : ℕ} (hk : 0 < k) :
    IsProbabilityMeasure (studentTMeasure k) where
  measure_univ := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hG1 : 0 < Gamma (((k : ℝ) + 1) / 2) := Gamma_pos_of_pos (by positivity)
    have hG2 : 0 < Gamma ((k : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
    have hsq : 0 < √(k * π) := sqrt_pos.mpr (by positivity)
    have hC : 0 ≤ Gamma (((k : ℝ) + 1) / 2) / (√(k * π) * Gamma ((k : ℝ) / 2)) := by
      positivity
    rw [studentTMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    simp_rw [ENNReal.ofReal_mul hC]
    rw [lintegral_const_mul _ (by fun_prop), show -((k : ℝ) + 1) / 2 = -(((k : ℝ) + 1) / 2) by
      ring, lintegral_one_add_sq_div_rpow_neg hk' (by linarith), ← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_one]
    congr 1
    rw [show ((k : ℝ) + 1) / 2 - 1 / 2 = k / 2 by ring]
    field_simp

/-! ### The ratio law -/

/-- Pointwise kernel identity behind the ratio law: the `χ²_k` density times the Jacobian
`√(v/k)` times the standard normal density at `√(v/k) t` is the `t_k` density at `t` times a
gamma density in `v`. -/
private lemma studentT_kernel_eq {k : ℕ} (hk : 0 < k) (t : ℝ) {v : ℝ} (hv : 0 < v) :
    gammaPDFReal ((k : ℝ) / 2) (1 / 2) v * √(v / k) * gaussianPDFReal 0 1 (√(v / k) * t) =
      Gamma ((k + 1) / 2) / (√(k * π) * Gamma (k / 2)) *
          (1 + t ^ 2 / k) ^ (-((k : ℝ) + 1) / 2) *
        gammaPDFReal (((k : ℝ) + 1) / 2) ((1 + t ^ 2 / k) / 2) v := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hL : 0 < 1 + t ^ 2 / k := by positivity
  have hG1 : 0 < Gamma (((k : ℝ) + 1) / 2) := Gamma_pos_of_pos (by positivity)
  have hG2 : 0 < Gamma ((k : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  simp only [gammaPDFReal, hv.le, ↓reduceIte, gaussianPDFReal, NNReal.coe_one, mul_one,
    sub_zero]
  have hexp : exp (-(1 / 2 * v)) * exp (-(√(v / k) * t) ^ 2 / 2) =
      exp (-((1 + t ^ 2 / k) / 2 * v)) := by
    rw [← exp_add, mul_pow, sq_sqrt (by positivity)]
    congr 1; field_simp; ring
  have hpow : v ^ ((k : ℝ) / 2 - 1) * √(v / k) = v ^ (((k : ℝ) + 1) / 2 - 1) / √k := by
    rw [sqrt_div hv.le, sqrt_eq_rpow v, mul_div_assoc', ← rpow_add hv]
    congr 2; ring
  have h2 : ((1 + t ^ 2 / k) / 2) ^ (((k : ℝ) + 1) / 2) =
      (1 + t ^ 2 / k) ^ (((k : ℝ) + 1) / 2) / ((2 : ℝ) ^ ((k : ℝ) / 2) * √2) := by
    rw [div_rpow hL.le (by norm_num), sqrt_eq_rpow, ← rpow_add (by norm_num)]
    congr 2; ring
  have hneg : (1 + t ^ 2 / k) ^ (-((k : ℝ) + 1) / 2) =
      ((1 + t ^ 2 / k) ^ (((k : ℝ) + 1) / 2))⁻¹ := by
    rw [neg_div, rpow_neg hL.le]
  have hhalf : (1 / 2 : ℝ) ^ ((k : ℝ) / 2) = ((2 : ℝ) ^ ((k : ℝ) / 2))⁻¹ := by
    rw [one_div, inv_rpow (by norm_num)]
  have hs2 : √(2 * π) = √2 * √π := sqrt_mul (by norm_num) π
  have hskp : √(k * π) = √k * √π := sqrt_mul hk'.le π
  have hLs : 0 < (1 + t ^ 2 / k) ^ (((k : ℝ) + 1) / 2) := rpow_pos_of_pos hL _
  have h2k : 0 < (2 : ℝ) ^ ((k : ℝ) / 2) := rpow_pos_of_pos (by norm_num) _
  have hsk : 0 < √(k : ℝ) := sqrt_pos.mpr hk'
  have hsp : 0 < √π := sqrt_pos.mpr pi_pos
  have hs2' : 0 < √(2 : ℝ) := sqrt_pos.mpr (by norm_num)
  calc _ = (1 / 2 : ℝ) ^ ((k : ℝ) / 2) / Gamma ((k : ℝ) / 2) *
        (v ^ ((k : ℝ) / 2 - 1) * √(v / k)) * (√(2 * π))⁻¹ *
        (exp (-(1 / 2 * v)) * exp (-(√(v / k) * t) ^ 2 / 2)) := by ring
    _ = _ := by
      rw [hexp, hpow, h2, hneg, hhalf, hs2, hskp]
      field_simp

/-- Linear substitution `z = σ t` for a lower Lebesgue integral on `ℝ`, `σ > 0`. -/
private lemma lintegral_comp_mul_left_of_pos {σ : ℝ} (hσ : 0 < σ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ z, F z = ENNReal.ofReal σ * ∫⁻ t, F (σ * t) := by
  conv_lhs => rw [← Real.smul_map_volume_mul_left hσ.ne']
  rw [lintegral_smul_measure, abs_of_pos hσ, smul_eq_mul]
  congr 1
  exact lintegral_map_equiv F (Homeomorph.mulLeft₀ σ hσ.ne').toMeasurableEquiv

/-- **Student's `t` law as a ratio** (Casella–Berger, Definition 5.3.4): for independent
`Z ~ N(0, 1)` and `V ~ χ²_k` with `k ≥ 1`, `Z / √(V / k)` has law `studentTMeasure k`. This
proves `ProbabilityTheory.NormalTheoryWanted.map_div_sqrt_chiSquare_eq_studentT` (whose right-hand
side is `studentTMeasure k` by definition). -/
theorem map_div_sqrt_chiSquare_eq_studentT {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ} (hk : 0 < k) {Z V : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P) (hV : HasLaw V (chiSquareMeasure k) P)
    (hZV : IndepFun Z V P) :
    P.map (fun ω => Z ω / √(V ω / k)) = studentTMeasure k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set g : ℝ × ℝ → ℝ := fun p => p.1 / √(p.2 / k) with hg_def
  have hg : Measurable g := by fun_prop
  have hprod : P.map (fun ω => (Z ω, V ω)) = (gaussianReal 0 1).prod (chiSquareMeasure k) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hV.aemeasurable).1 hZV,
      hZ.map_eq, hV.map_eq]
  have hcomp : P.map (fun ω => Z ω / √(V ω / k)) = (P.map (fun ω => (Z ω, V ω))).map g := by
    rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable
      (hZ.aemeasurable.prodMk hV.aemeasurable)]
    rfl
  rw [hcomp, hprod]
  have := isProbabilityMeasure_chiSquareMeasure hk
  ext s hs
  have hind : Measurable (s.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hs
  rw [Measure.map_apply hg hs, studentTMeasure, withDensity_apply _ hs,
    ← lintegral_indicator_one (hg hs),
    lintegral_prod_symm _ ((measurable_one.indicator (hg hs)).aemeasurable)]
  have hgs : Measurable ((g ⁻¹' s).indicator (1 : ℝ × ℝ → ℝ≥0∞)) :=
    measurable_one.indicator (hg hs)
  set K : ℝ → ℝ → ℝ≥0∞ := fun v t => gammaPDF ((k : ℝ) / 2) (1 / 2) v *
    (ENNReal.ofReal √(v / k) * gaussianPDF 0 1 (√(v / k) * t)) with hK_def
  have hinner : ∀ v : ℝ, 0 < v → ∫⁻ z, (g ⁻¹' s).indicator 1 (z, v) ∂gaussianReal 0 1 =
      ∫⁻ t in s, ENNReal.ofReal √(v / k) * gaussianPDF 0 1 (√(v / k) * t) := by
    intro v hv
    have hσ : 0 < √(v / k) := sqrt_pos.mpr (by positivity)
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
        (g := fun z => (g ⁻¹' s).indicator 1 (z, v)) (hgs.comp measurable_prodMk_right),
      lintegral_comp_mul_left_of_pos hσ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator hs]
    congr 1
    funext t
    have hgt : g (√(v / k) * t, v) = t := by
      rw [hg_def]; exact mul_div_cancel_left₀ t hσ.ne'
    have hmem : (√(v / k) * t, v) ∈ g ⁻¹' s ↔ t ∈ s := by rw [Set.mem_preimage, hgt]
    simp only [Set.indicator, Pi.mul_apply, Pi.one_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd (hmem.1 h1) h2
    · exact absurd (hmem.2 h2) h1
    · simp
  have houter : ∀ᵐ v ∂(volume : Measure ℝ), gammaPDF ((k : ℝ) / 2) (1 / 2) v *
      ∫⁻ z, (g ⁻¹' s).indicator 1 (z, v) ∂gaussianReal 0 1 = ∫⁻ t in s, K v t := by
    filter_upwards [Measure.ae_ne volume 0] with v hv
    rcases lt_or_gt_of_ne hv with hv' | hv'
    · simp [hK_def, gammaPDF_of_neg hv']
    · rw [hinner v hv', ← lintegral_const_mul' _ _ (by simp [gammaPDF])]
  have hKm : Measurable (Function.uncurry K) := by
    refine ((measurable_gammaPDF _ _).comp measurable_fst).mul ?_
    refine (by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal √(p.1 / k)).mul ?_
    exact (measurable_gaussianPDF 0 1).comp (by fun_prop)
  rw [chiSquareMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_gammaPDF _ _) hgs.lintegral_prod_left']
  simp only [Pi.mul_apply]
  rw [lintegral_congr_ae houter, lintegral_lintegral_swap hKm.aemeasurable]
  refine setLIntegral_congr_fun hs (fun t _ => ?_)
  have hlam : 0 < (1 + t ^ 2 / k) / 2 := by positivity
  have hdens : 0 ≤ Gamma ((k + 1) / 2) / (√(k * π) * Gamma (k / 2)) *
      (1 + t ^ 2 / k) ^ (-((k : ℝ) + 1) / 2) := by
    have := Gamma_pos_of_pos (by positivity : (0 : ℝ) < ((k : ℝ) + 1) / 2)
    have := Gamma_pos_of_pos (by positivity : (0 : ℝ) < (k : ℝ) / 2)
    have : 0 < 1 + t ^ 2 / k := by positivity
    positivity
  have hae : (fun v => K v t) =ᵐ[volume] fun v => ENNReal.ofReal
      (Gamma ((k + 1) / 2) / (√(k * π) * Gamma (k / 2)) *
        (1 + t ^ 2 / k) ^ (-((k : ℝ) + 1) / 2)) *
      gammaPDF (((k : ℝ) + 1) / 2) ((1 + t ^ 2 / k) / 2) v := by
    filter_upwards [Measure.ae_ne volume 0] with v hv
    rcases lt_or_gt_of_ne hv with hv' | hv'
    · simp [hK_def, gammaPDF_of_neg hv']
    · simp only [hK_def, gammaPDF, gaussianPDF]
      rw [← ENNReal.ofReal_mul (sqrt_nonneg _),
        ← ENNReal.ofReal_mul (gammaPDFReal_nonneg (by positivity) (by norm_num) _),
        ← ENNReal.ofReal_mul hdens, ← studentT_kernel_eq hk t hv', mul_assoc]
  rw [lintegral_congr_ae hae, lintegral_const_mul _ (measurable_gammaPDF _ _),
    lintegral_gammaPDF_eq_one (by positivity) hlam, mul_one]

end

end

end ProbabilityTheory
