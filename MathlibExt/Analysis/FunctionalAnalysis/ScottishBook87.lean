/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Nonlinear interpolation on Lebesgue spaces

`nonlinearInterpolationLp` proves the intermediate norm bound in Scottish Book Problem 87
by integrating distribution estimates for the large and small parts of the input.
-/

public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook87Wanted

open MeasureTheory Set Filter
open scoped ENNReal

/-- The heights at which the endpoint with exponent `p` controls an input of size `u`. -/
private noncomputable def heights (p g u : ℝ) : Set ℝ := if p < g then Iic u else Ioi u

private noncomputable def kernel (p g t u : ℝ) : ℝ≥0∞ :=
  (heights p g u).indicator (fun t ↦ ENNReal.ofReal ((u / t) ^ p)) t

private lemma integral_power_on_heights {p g u : ℝ} (hu : 0 < u) (hpg : p ≠ g) :
    ∫ t in heights p g u ∩ Ioi 0, t ^ (g - p - 1) =
      u ^ (g - p) / |g - p| := by
  by_cases h : p < g
  · have hd : 0 < g - p := sub_pos.mpr h
    rw [heights, ite_eq_left h, inter_comm, Ioi_inter_Iic, ← intervalIntegral.integral_of_le hu.le,
      integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.zero_rpow hd.ne',
      sub_zero, abs_of_pos hd]
  · have hd : g - p < 0 := by rcases lt_or_gt_of_ne hpg with hh | hh <;> linarith
    rw [heights, ite_eq_right h, inter_eq_left.mpr (Ioi_subset_Ioi hu.le),
      integral_Ioi_rpow_of_lt (by linarith) hu, sub_add_cancel, abs_of_neg hd, div_neg, neg_div]

private lemma integrate_kernel {p g u : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hg : 0 < g) (hpg : p ≠ g) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (g - 1)) * kernel p g t u =
      ENNReal.ofReal (1 / |g - p|) * ENNReal.ofReal (u ^ g) := by
  rcases hu.eq_or_lt with rfl | hu
  · rw [Real.zero_rpow hg.ne', ENNReal.ofReal_zero, mul_zero]
    apply setLIntegral_eq_zero measurableSet_Ioi
    intro t ht
    by_cases h : p < g
    · simp [kernel, heights, h, not_le.mpr (mem_Ioi.mp ht)]
    · have hp' : p ≠ 0 := by rintro rfl; exact h hg
      simp [kernel, heights, h, ht, Real.zero_rpow hp']
  have hm : MeasurableSet (heights p g u) := by
    unfold heights
    split <;> measurability
  have eqn (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      ENNReal.ofReal (t ^ (g - 1)) * kernel p g t u =
        ENNReal.ofReal (u ^ p) * (heights p g u).indicator
          (fun t ↦ ENNReal.ofReal (t ^ (g - p - 1))) t := by
    have ht' : 0 < t := ht
    by_cases h : t ∈ heights p g u
    · simp only [kernel, indicator_of_mem h]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht'.le _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _), Real.div_rpow hu.le ht'.le,
        show g - p - 1 = (g - 1) - p by ring, Real.rpow_sub ht' (g - 1) p]
      congr 1
      ring
    · simp [kernel, h]
  have hi : IntegrableOn (fun t : ℝ ↦ t ^ (g - p - 1)) (heights p g u ∩ Ioi 0) := by
    by_cases h : p < g
    · rw [heights, ite_eq_left h, inter_comm, Ioi_inter_Iic]
      exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1
    · rw [heights, ite_eq_right h, inter_eq_left.mpr (Ioi_subset_Ioi hu.le)]
      exact integrableOn_Ioi_rpow_of_lt (by rcases lt_or_gt_of_ne hpg with hh | hh <;> linarith) hu
  have hnn : ∀ᵐ t ∂volume.restrict (heights p g u ∩ Ioi 0), 0 ≤ t ^ (g - p - 1) := by
    filter_upwards [ae_restrict_mem (hm.inter measurableSet_Ioi)] with t ht
    exact Real.rpow_nonneg (le_of_lt ht.2) _
  rw [setLIntegral_congr_fun measurableSet_Ioi eqn, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator hm, Measure.restrict_restrict hm,
    ← ofReal_integral_eq_lintegral_ofReal hi hnn, integral_power_on_heights hu hpg,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← mul_div_assoc, ← Real.rpow_add hu]
  ring_nf

private lemma measurable_kernel (p g : ℝ) :
    Measurable fun z : ℝ × ℝ ↦ kernel p g z.1 z.2 := by
  simp only [kernel, heights]
  split <;> exact Measurable.ite (by first | exact measurableSet_le measurable_fst measurable_snd
                                           | exact measurableSet_lt measurable_snd measurable_fst)
      (by fun_prop) measurable_const

variable {μ : Measure ℝ}

private noncomputable def layer (μ : Measure ℝ) (p g t : ℝ) (f : ℝ → ℝ) :=
  ∫⁻ x, kernel p g t (f x) ∂μ

private lemma layer_measurable [IsFiniteMeasure μ] {f : ℝ → ℝ} (hf : AEMeasurable f μ) (p g : ℝ)
    (ν : Measure ℝ) [SFinite ν] : AEMeasurable (fun t ↦ layer μ p g t f) ν :=
  (AEMeasurable.lintegral_prod_right (f := fun t x ↦ kernel p g t (f x))
    ((measurable_kernel p g).comp_aemeasurable (measurable_fst.aemeasurable.prodMk hf.comp_snd)))

private lemma integrate_layer [IsFiniteMeasure μ] {p g : ℝ} {f : ℝ → ℝ}
    (hf : AEMeasurable f μ) (hfn : 0 ≤ f) (hp : 0 ≤ p) (hg : 0 < g) (hpg : p ≠ g) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (g - 1)) * layer μ p g t f =
      ENNReal.ofReal (1 / |g - p|) * ∫⁻ x, ENNReal.ofReal (f x ^ g) ∂μ := by
  simp_rw [layer, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap]
  · simp_rw [integrate_kernel (hfn _) hp hg hpg]
  · exact (show Measurable (fun z : ℝ × ℝ ↦ ENNReal.ofReal (z.1 ^ (g - 1))) by fun_prop)
      |>.aemeasurable.mul ((measurable_kernel p g).comp_aemeasurable
        (measurable_fst.aemeasurable.prodMk hf.comp_snd))

private lemma layer_zero {g : ℝ} (hg : 0 < g) (t : ℝ) {f : ℝ → ℝ} (hf : AEMeasurable f μ) :
    layer μ 0 g t f = μ {x | t ≤ f x} := by
  have hs := nullMeasurableSet_le (aemeasurable_const (b := t)) hf
  rw [← lintegral_indicator_one₀ hs]
  simp [layer, kernel, heights, hg, indicator_apply]

private lemma moment_eq_norm_pow {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.toReal) ∂μ = eLpNorm f p μ ^ p.toReal := by
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ofReal_norm]
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp hp' hf, ← ENNReal.rpow_mul,
    one_div_mul_cancel (ENNReal.toReal_pos hp hp').ne', ENNReal.rpow_one]

/-- Chebyshev's estimate at height `C * t`, given an endpoint norm bound by `C`. -/
private lemma endpoint_tail {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) {v w : ℝ → ℝ}
    (hv : MemLp v p μ) (hw : MemLp w p μ) {C t : ℝ} (hC : 0 < C) (ht : 0 < t)
    (hb : (eLpNorm w p μ).toReal ≤ C * (eLpNorm v p μ).toReal) :
    μ {x | C * t ≤ ‖w x‖} ≤ ∫⁻ x, ENNReal.ofReal ((‖v x‖ / t) ^ p.toReal) ∂μ := by
  have hE := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_toReal hw.eLpNorm_lt_top.ne, ENNReal.ofReal_mul hC.le,
    ENNReal.ofReal_toReal hv.eLpNorm_lt_top.ne] at hE
  have hCt := mul_pos hC ht
  have hcancel : (ENNReal.ofReal (C * t))⁻¹ * ENNReal.ofReal C = ENNReal.ofReal t⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos hCt, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc
    μ {x | C * t ≤ ‖w x‖}
      = μ {x | ENNReal.ofReal (C * t) ≤ ‖w x‖ₑ} := by
          simp only [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
    _ ≤ _ := meas_ge_le_mul_pow_eLpNorm_eNorm μ hp hp'
          (ENNReal.ofReal_pos.mpr hCt).ne' (by simp)
    _ ≤ (ENNReal.ofReal (C * t))⁻¹ ^ p.toReal *
          (ENNReal.ofReal C * eLpNorm v p μ) ^ p.toReal := by gcongr
    _ = ENNReal.ofReal ((t⁻¹) ^ p.toReal) * ∫⁻ x, ENNReal.ofReal (‖v x‖ ^ p.toReal) ∂μ := by
          rw [moment_eq_norm_pow hp hp' hv.aestronglyMeasurable,
            ← ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
            ← mul_assoc, hcancel, ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
            ENNReal.ofReal_rpow_of_pos (inv_pos.mpr ht)]
    _ = _ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ← Real.mul_rpow (by positivity) (norm_nonneg _), div_eq_inv_mul]

private noncomputable def lowPart (f : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  {x | ‖f x‖ < t}.indicator f

private lemma lowPart_bound (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖lowPart f t x‖ ≤ t := by
  by_cases h : |f x| < t
  · simpa [lowPart, indicator_apply, h] using h.le
  · simpa [lowPart, indicator_apply, h] using ht.le

private lemma lowPart_memLp {f : ℝ → ℝ} (hf : AEStronglyMeasurable f μ) {t : ℝ} (ht : 0 < t) :
    MemLp (lowPart f t) ⊤ μ :=
  memLp_top_of_bound (hf.indicator₀ (nullMeasurableSet_lt hf.norm.aemeasurable aemeasurable_const))
    t (.of_forall (lowPart_bound f ht))

private lemma layer_low {p g : ℝ} (hp : 0 < p) (hpg : g < p) (t : ℝ) (f : ℝ → ℝ) :
    layer μ p g t (fun x ↦ ‖f x‖) =
      ∫⁻ x, ENNReal.ofReal ((‖lowPart f t x‖ / t) ^ p) ∂μ := by
  apply lintegral_congr
  intro x
  by_cases h : |f x| < t <;>
    simp [kernel, heights, lowPart, hpg.not_gt, h, Real.zero_rpow hp.ne']

private lemma layer_high {p g : ℝ} (hp : 0 < p) (hpg : p < g) (t : ℝ) (f : ℝ → ℝ) :
    layer μ p g t (fun x ↦ ‖f x‖) =
      ∫⁻ x, ENNReal.ofReal ((‖(f - lowPart f t) x‖ / t) ^ p) ∂μ := by
  apply lintegral_congr
  intro x
  by_cases h : |f x| < t
  · simp [kernel, heights, lowPart, hpg, h, h.not_ge, Real.zero_rpow hp.ne']
  · simp [kernel, heights, lowPart, hpg, h, le_of_not_gt h]

/-- At an infinite upper endpoint the small part contributes zero to the output tail. -/
private lemma top_tail {v w : ℝ → ℝ} {M C t : ℝ} (hM : 0 ≤ M) (hC : M < C)
    (ht : 0 < t) (hv : MemLp v ⊤ μ) (hw : MemLp w ⊤ μ) (hv' : ∀ x, ‖v x‖ ≤ t)
    (hb : (eLpNorm w ⊤ μ).toReal ≤ M * (eLpNorm v ⊤ μ).toReal) :
    μ {x | C * t ≤ ‖w x‖} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  have hev := eLpNormEssSup_le_of_ae_bound (μ := μ) (.of_forall hv')
  have hev' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hev
  rw [← eLpNorm_exponent_top hv.aestronglyMeasurable, ENNReal.toReal_ofReal ht.le] at hev'
  filter_upwards [eNorm_ae_le_eLpNormEssSup w μ] with x hx
  rw [← eLpNorm_exponent_top hw.aestronglyMeasurable] at hx
  have hx' := ENNReal.toReal_mono hw.eLpNorm_lt_top.ne hx
  rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] at hx'
  exact not_le.mpr ((hx'.trans (hb.trans (mul_le_mul_of_nonneg_left hev' hM))).trans_lt
    (mul_lt_mul_of_pos_right hC ht))

private lemma integrate_tail_bound [IsFiniteMeasure μ] {a b g : ℝ} (hb : 0 < b) (hbg : b < g)
    (hga : g < a) {f y : ℝ → ℝ} (hf : AEMeasurable f μ) (hfn : 0 ≤ f)
    (hy : AEMeasurable y μ) (hyn : 0 ≤ y)
    (htail : ∀ t > 0, μ {x | t ≤ y x} ≤ layer μ b g t f + layer μ a g t f) :
    ENNReal.ofReal (1 / g) * (∫⁻ x, ENNReal.ofReal (y x ^ g) ∂μ) ≤
      (ENNReal.ofReal (1 / |g - b|) + ENNReal.ofReal (1 / |g - a|)) *
        ∫⁻ x, ENNReal.ofReal (f x ^ g) ∂μ := by
  have hg := hb.trans hbg
  let W (t : ℝ) := ENNReal.ofReal (t ^ (g - 1))
  have hW : Measurable W := by dsimp [W]; fun_prop
  have h : (∫⁻ t in Ioi 0, W t * layer μ 0 g t y) ≤
      ∫⁻ t in Ioi 0, W t * (layer μ b g t f + layer μ a g t f) :=
    setLIntegral_mono' measurableSet_Ioi fun t ht ↦
      mul_le_mul_of_nonneg_left ((layer_zero hg t hy).le.trans (htail t ht)) zero_le
  simp only [mul_add] at h
  have hm := hW.aemeasurable.fun_mul (layer_measurable hf b g (volume.restrict (Ioi 0)))
  rw [lintegral_add_left' hm] at h
  simpa only [W, integrate_layer hy hyn le_rfl hg hg.ne,
    integrate_layer hf hfn hb.le hg hbg.ne, integrate_layer hf hfn (hg.trans hga).le hg hga.ne',
    sub_zero, abs_of_pos hg, add_mul] using h

/-- Take the positive root of the integrated tail bound, retaining finiteness in `ℝ≥0∞`. -/
private lemma norm_bound_of_tails [IsFiniteMeasure μ] {a b : ℝ} {γ : ℝ≥0∞}
    (hγ : γ ≠ 0) (hγ' : γ ≠ ⊤) (hb : 0 < b) (hbg : b < γ.toReal) (hga : γ.toReal < a)
    {D : ℝ} (hD : 0 < D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f y : ℝ → ℝ, MemLp f γ μ → AEStronglyMeasurable y μ →
      (∀ t > 0, μ {x | D * t ≤ ‖y x‖} ≤
        layer μ b γ.toReal t (fun x ↦ ‖f x‖) + layer μ a γ.toReal t (fun x ↦ ‖f x‖)) →
      MemLp y γ μ ∧ (eLpNorm y γ μ).toReal ≤ M * (eLpNorm f γ μ).toReal := by
  let g := γ.toReal
  have hg : 0 < g := hb.trans hbg
  let A := ENNReal.ofReal (1 / g) * ENNReal.ofReal ((D⁻¹) ^ g)
  let B := ENNReal.ofReal (1 / |g - b|) + ENNReal.ofReal (1 / |g - a|)
  have hA : A ≠ 0 := by dsimp [A]; positivity
  have hA' : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  let K := (A⁻¹ * B) ^ (1 / g)
  have hK : K ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA) (by dsimp [B]; finiteness)
  refine ⟨K.toReal, ENNReal.toReal_nonneg, fun f y hf hy ht ↦ ?_⟩
  have hs (t : ℝ) : {x | t ≤ D⁻¹ * ‖y x‖} = {x | D * t ≤ ‖y x‖} := by
    ext x
    simp only [mem_ofPred_eq, ← div_eq_inv_mul, le_div_iff₀ hD, mul_comm t D]
  have hi := integrate_tail_bound hb hbg hga hf.aestronglyMeasurable.norm.aemeasurable
    (fun x ↦ norm_nonneg _) (aemeasurable_const.mul hy.norm.aemeasurable)
    (fun x ↦ mul_nonneg (inv_nonneg.mpr hD.le) (norm_nonneg _))
    (fun t ht' ↦ (hs t) ▸ ht t ht')
  have hm : A * eLpNorm y γ μ ^ g ≤ B * eLpNorm f γ μ ^ g := by
    dsimp only [Pi.mul_apply] at hi
    simp_rw [Real.mul_rpow (inv_nonneg.mpr hD.le) (norm_nonneg _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hD.le) _)] at hi
    rwa [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
      moment_eq_norm_pow hγ hγ' hy, moment_eq_norm_pow hγ hγ' hf.aestronglyMeasurable] at hi
  have h := mul_le_mul_of_nonneg_left hm (show 0 ≤ A⁻¹ from zero_le)
  rw [← mul_assoc, ENNReal.inv_mul_cancel hA hA', one_mul, ← mul_assoc] at h
  have hn := ENNReal.rpow_le_rpow h (show 0 ≤ 1 / g by positivity)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hg.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_one_div_cancel hg.ne',
    ENNReal.rpow_one] at hn
  have hfin := ENNReal.mul_ne_top hK hf.eLpNorm_lt_top.ne
  refine ⟨hn.trans_lt hfin.lt_top, ?_⟩
  simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono hfin hn

set_option linter.unusedVariables false in
/--
**Nonlinear interpolation of Lipschitz maps on Lebesgue spaces (Scottish Book Problem 87).**
Let $\mu$ be Lebesgue measure on $[0, 1]$, write $\|f\|_p$ for the $L^p(\mu)$ norm, let
$1 \le \beta < \alpha \le \infty$, and let $U$ map functions $\mathbb{R} \to \mathbb{R}$ to
functions $\mathbb{R} \to \mathbb{R}$. Suppose that $U$ maps $L^\beta(\mu)$ into $L^\beta(\mu)$;
that there is $L \ge 0$ with $\|Ux - Uy\|_\beta \le L \|x - y\|_\beta$ for all
$x, y \in L^\beta(\mu)$; and that there is $M_\alpha \ge 0$ such that every $x \in L^\alpha(\mu)$
has $Ux \in L^\alpha(\mu)$ and $\|Ux\|_\alpha \le M_\alpha \|x\|_\alpha$. Then for every $\gamma$
with $\beta < \gamma < \alpha$ there is $M_\gamma \ge 0$ such that every $x \in L^\gamma(\mu)$
has $Ux \in L^\gamma(\mu)$ and $\|Ux\|_\gamma \le M_\gamma \|x\|_\gamma$.

Source: S. Banach, Problem 87 of the Scottish Book;
affirmative solution by L. Maligranda, commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015). The linear case follows from
the Riesz interpolation theorem, and Banach showed the case `α = ∞`;
Maligranda's solution covers the nonlinear case as stated here, with
`α = ⊤` allowed.
-/
theorem nonlinearInterpolationLp :
    ∀ (β α : ℝ≥0∞) (hβ : 1 ≤ β) (hα : β < α)
      (U : (ℝ → ℝ) → (ℝ → ℝ)),
      (∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ → ℝ,
        MeasureTheory.MemLp x β (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
        MeasureTheory.MemLp y β (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
        (MeasureTheory.eLpNorm (U x - U y) β
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤
          L * (MeasureTheory.eLpNorm (x - y) β
            (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) →
      (∀ x : ℝ → ℝ,
        MeasureTheory.MemLp x β (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
        MeasureTheory.MemLp (U x) β (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))) →
      (∃ Mα : ℝ, 0 ≤ Mα ∧ ∀ x : ℝ → ℝ,
        MeasureTheory.MemLp x α (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
        MeasureTheory.MemLp (U x) α (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
        (MeasureTheory.eLpNorm (U x) α
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤
          Mα * (MeasureTheory.eLpNorm x α
            (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) →
      ∀ γ : ℝ≥0∞, β < γ → γ < α →
        ∃ Mγ : ℝ, 0 ≤ Mγ ∧ ∀ x : ℝ → ℝ,
          MeasureTheory.MemLp x γ (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
          MeasureTheory.MemLp (U x) γ (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
          (MeasureTheory.eLpNorm (U x) γ
            (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤
            Mγ * (MeasureTheory.eLpNorm x γ
              (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  intro β α hβ hα U ⟨L, hL, hlip⟩ hmap ⟨M, hM, hbound⟩ γ hβγ hγα
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have hb₀ : β ≠ 0 := (zero_lt_one.trans_le hβ).ne'
  have hg₀ : γ ≠ 0 := (zero_le.trans_lt hβγ).ne'
  have hb := ENNReal.toReal_pos hb₀ hα.ne_top
  have hbg := (ENNReal.toReal_lt_toReal hα.ne_top hγα.ne_top).mpr hβγ
  -- A finite surrogate exponent suffices when the small-part output tail vanishes.
  let a := if α = ⊤ then γ.toReal + 1 else α.toReal
  have hga : γ.toReal < a := by
    dsimp [a]
    split
    · linarith
    · exact (ENNReal.toReal_lt_toReal hγα.ne_top ‹α ≠ ⊤›).mpr hγα
  let C := L + M + 1
  have hC : 0 < C := by dsimp [C]; linarith
  have hLC : L ≤ C := by dsimp [C]; linarith
  have hMC : M < C := by dsimp [C]; linarith
  obtain ⟨K, hK, hinterp⟩ := norm_bound_of_tails (μ := μ) hg₀ hγα.ne_top hb hbg hga
    (D := 2 * C) (by positivity)
  refine ⟨K, hK, fun f hf ↦ ?_⟩
  have hfβ := hf.mono_exponent hβγ.le
  have hUβ := hmap f hfβ
  apply hinterp f (U f) hf hUβ.aestronglyMeasurable
  intro t ht
  let v := lowPart f t
  have hv := lowPart_memLp hf.aestronglyMeasurable ht
  have hvβ : MemLp v β μ := hv.mono_exponent le_top
  have hvα : MemLp v α μ := hv.mono_exponent le_top
  have high : μ {x | C * t ≤ ‖(U f - U v) x‖} ≤ layer μ β.toReal γ.toReal t (fun x ↦ ‖f x‖) := by
    rw [layer_high hb hbg]
    exact endpoint_tail hb₀ hα.ne_top (hfβ.sub hvβ) (hUβ.sub (hmap v hvβ)) hC ht
      ((hlip f v hfβ hvβ).trans (mul_le_mul_of_nonneg_right hLC ENNReal.toReal_nonneg))
  obtain ⟨hvU, hvB⟩ := hbound v hvα
  have low : μ {x | C * t ≤ ‖U v x‖} ≤ layer μ a γ.toReal t (fun x ↦ ‖f x‖) := by
    by_cases h : α = ⊤
    · subst α
      rw [top_tail hM hMC ht hv hvU (lowPart_bound f ht) hvB]
      exact zero_le
    · have ha : a = α.toReal := by simp [a, h]
      rw [layer_low (hb.trans (hbg.trans hga)) hga, ha]
      exact endpoint_tail (zero_le.trans_lt hα).ne' h hvα hvU hC ht
        (hvB.trans (mul_le_mul_of_nonneg_right hMC.le ENNReal.toReal_nonneg))
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add high low))
  intro x hx
  change 2 * C * t ≤ ‖U f x‖ at hx
  change C * t ≤ ‖U f x - U v x‖ ∨ C * t ≤ ‖U v x‖
  have htr := norm_add_le (U f x - U v x) (U v x)
  rw [sub_add_cancel] at htr
  by_contra! h
  linarith [h.1, h.2]

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook87Wanted
