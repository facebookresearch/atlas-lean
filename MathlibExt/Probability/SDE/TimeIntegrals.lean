/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.ItoIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Ordinary integrals of progressive processes

The actual time primitive of a progressive process is adapted. Continuous input
paths give continuous and progressive primitives. Cauchy–Schwarz bounds the
squared primitive by elapsed time times the integrated squared input.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- The actual ordinary time integral of a progressive process is adapted to the
same filtration. No completeness or path continuity is required. -/
theorem IsProgressive.adapted_timeIntegral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) :
    Adapted F (fun t ω ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal ω) := by
  intro t
  let := F t
  have hg : Measurable fun p : ℝ × Ω ↦ H (min p.1.toNNReal t) p.2 := by
    have hm : Measurable fun p : ℝ × Ω ↦
        ((⟨min p.1.toNNReal t, min_le_right _ _⟩ : Iic t), p.2) :=
      ((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk.prodMk
        measurable_snd
    exact (hH t).comp hm
  have hi := (hg.stronglyMeasurable.integral_prod_left
    (μ := volume.restrict (Ioc (0 : ℝ) t))
    (f := fun s ω ↦ H (min s.toNNReal t) ω)).measurable
  convert hi using 1
  funext ω
  dsimp only
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  dsimp only
  rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]

/-- A continuous path has a continuous ordinary time primitive on nonnegative time. -/
theorem continuous_timeIntegral {H : ℝ≥0 → ℝ} (hH : Continuous H) :
    Continuous (fun t : ℝ≥0 ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal) :=
  (intervalIntegral.differentiable_integral_of_continuous
    (hH.comp continuous_real_toNNReal)).continuous.comp NNReal.continuous_coe

/-- The actual time primitive of a progressive process with continuous paths is progressive. -/
theorem IsProgressive.timeIntegral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hc : ∀ ω, Continuous (H · ω)) :
    IsProgressive F (fun t ω ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal ω) := by
  have ha : Adapted F (fun t ω ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal ω) :=
    IsProgressive.adapted_timeIntegral hH
  exact (ha.stronglyAdapted.isStronglyProgressive_of_continuous
    (fun ω ↦ continuous_timeIntegral (hc ω))).isProgressive

private theorem sq_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, f ω ∂μ)^2 ≤ μ.real univ * ∫ ω, (f ω)^2 ∂μ := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by simpa using hf
  have hg : MemLp (fun _ : Ω ↦ (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const _
  have h := integral_mul_norm_le_Lp_mul_Lq hpq hf' hg
  have he : (∫ ω, |f ω| ∂μ) ≤
      Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (μ.real univ) := by
    simpa only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs, one_pow,
      integral_const, smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] using h
  have ha : |∫ ω, f ω ∂μ| ≤ ∫ ω, |f ω| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
  have hs := pow_le_pow_left₀ (abs_nonneg _) (ha.trans he) 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
    Real.sq_sqrt (measureReal_nonneg)] at hs
  simpa only [mul_comm] using hs

/-- **Squared ordinary-integral bound.** For a continuous real function $H$ on nonnegative time and
$t \ge 0$,
$$\left|\int_0^t H_s\,ds\right|^2 \le t \int_{(0,t]} |H_s|^2\,ds,$$
in extended nonnegative real form. This is the Cauchy–Schwarz inequality
$$\left(\int_{(0,t]} |H_s| \cdot 1\,ds\right)^2 \le
  \int_{(0,t]} 1\,ds \cdot \int_{(0,t]} |H_s|^2\,ds$$
for $H$ and the constant function $1$ on $(0, t]$. -/
theorem enorm_timeIntegral_sq_le {H : ℝ≥0 → ℝ} (hH : Continuous H) (t : ℝ≥0) :
    ‖∫ s in (0 : ℝ)..t, H s.toNNReal‖ₑ^2 ≤
      (t : ℝ≥0∞) * ∫⁻ s in Ioc (0 : ℝ) t, ‖H s.toNNReal‖ₑ^2 := by
  have hc := hH.comp continuous_real_toNNReal
  have hsq : IntegrableOn (fun s ↦ (H s.toNNReal)^2) (Ioc (0 : ℝ) t) :=
    ((hc.pow 2).intervalIntegrable 0 t).1
  have hm : MemLp (fun s ↦ H s.toNNReal) 2 (volume.restrict (Ioc (0 : ℝ) t)) :=
    (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2 hsq
  have h := ENNReal.ofReal_le_ofReal (sq_integral_le hm)
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  simp only [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [← ofReal_integral_eq_lintegral_ofReal hsq
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
  simpa only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_zero, ENNReal.toReal_ofReal t.coe_nonneg, ENNReal.coe_toReal,
    ENNReal.ofReal_mul t.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] using! h

/-- **Lower-integral bound for an ordinary time integral.** Let $P$ be a measure and $H$ a real
process indexed by nonnegative time whose paths are continuous for every sample. For $t \ge 0$,
$$\int_\Omega \left|\int_0^t H_s(\omega)\,ds\right|^2 dP(\omega) \le
  t \int_\Omega \int_{(0,t]} |H_s(\omega)|^2\,ds\,dP(\omega).$$
Both sides are lower integrals of nonnegative functions, so no measurability in the sample variable
is required; the right side is $t$ times the input energy of $H$ up to $t$. -/
theorem lintegral_timeIntegral_sq_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {H : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous (H · ω)) (t : ℝ≥0) :
    ∫⁻ ω, ‖∫ s in (0 : ℝ)..t, H s.toNNReal ω‖ₑ^2 ∂P ≤
      (t : ℝ≥0∞) * integrandDist P H (fun _ _ ↦ 0) t := by
  calc
    _ ≤ ∫⁻ ω, (t : ℝ≥0∞) * (∫⁻ s in Ioc (0 : ℝ) t, ‖H s.toNNReal ω‖ₑ^2) ∂P :=
      lintegral_mono fun ω ↦ enorm_timeIntegral_sq_le (hc ω) t
    _ = _ := by simp only [lintegral_const_mul' _ _ (by simp : (t : ℝ≥0∞) ≠ ∞),
      integrandDist, sub_zero]

/-- **Square integrability of ordinary time integrals.** Let $P$ be a measure and $H$ a real process
indexed by nonnegative time that is progressively measurable for a filtration on the same space and
whose paths are continuous for every sample. If $H$ has finite input energy up to time $t$,
$$\int_\Omega \int_{(0,t]} |H_s(\omega)|^2\,ds\,dP(\omega) < \infty,$$
then the time integral $\omega \mapsto \int_0^t H_s(\omega)\,ds$ belongs to $L^2(P)$. -/
theorem memLp_timeIntegral {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hc : ∀ ω, Continuous (H · ω)) (t : ℝ≥0)
    (hH2 : integrandDist P H (fun _ _ ↦ 0) t ≠ ∞) :
    MemLp (fun ω ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal ω) 2 P := by
  have hmeas := (IsProgressive.adapted_timeIntegral hH t).mono (F.le t) le_rfl
  have hm := hmeas.aestronglyMeasurable (μ := P)
  apply (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
    (by norm_num) (by norm_num) hm).2
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    (lintegral_timeIntegral_sq_le P hc t).trans_lt
      (ENNReal.mul_ne_top (by simp) hH2).lt_top

/-- **Uniform bound for the ordinary primitive.** For a continuous real function $H$ on nonnegative
time and $T \ge 0$,
$$\sup_{0 \le t \le T} \left|\int_0^t H_s\,ds\right|^2 \le T \int_{(0,T]} |H_s|^2\,ds,$$
with the supremum taken in the extended nonnegative reals. It enlarges each fixed-time
Cauchy–Schwarz bound $\left|\int_0^t H_s\,ds\right|^2 \le t \int_{(0,t]} |H_s|^2\,ds$ to the
horizon $T$. -/
theorem iSup_enorm_timeIntegral_sq_le {H : ℝ≥0 → ℝ} (hH : Continuous H) (T : ℝ≥0) :
    (⨆ (t : ℝ≥0) (_ : t ≤ T), ‖∫ s in (0 : ℝ)..t, H s.toNNReal‖ₑ^2) ≤
      (T : ℝ≥0∞) * ∫⁻ s in Ioc (0 : ℝ) T, ‖H s.toNNReal‖ₑ^2 := by
  refine iSup₂_le fun t ht ↦ (enorm_timeIntegral_sq_le hH t).trans ?_
  exact mul_le_mul' (by exact_mod_cast ht)
    (lintegral_mono_set (Ioc_subset_Ioc_right (by exact_mod_cast ht)))

/-- **Lower-integral bound for the running maximum of a time integral.** Let $P$ be a measure and
$H$ a real process indexed by nonnegative time whose paths are continuous for every sample. For
$T \ge 0$,
$$\int_\Omega \sup_{0 \le t \le T} \left|\int_0^t H_s(\omega)\,ds\right|^2 dP(\omega) \le
  T \int_\Omega \int_{(0,T]} |H_s(\omega)|^2\,ds\,dP(\omega).$$
Both sides are lower integrals of nonnegative functions, so no measurability in the sample variable
is required. -/
theorem lintegral_iSup_timeIntegral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {H : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous (H · ω)) (T : ℝ≥0) :
    ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : t ≤ T),
      ‖∫ s in (0 : ℝ)..t, H s.toNNReal ω‖ₑ^2) ∂P ≤
        (T : ℝ≥0∞) * integrandDist P H (fun _ _ ↦ 0) T := by
  calc
    _ ≤ ∫⁻ ω, (T : ℝ≥0∞) * (∫⁻ s in Ioc (0 : ℝ) T, ‖H s.toNNReal ω‖ₑ^2) ∂P :=
      lintegral_mono fun ω ↦ iSup_enorm_timeIntegral_sq_le (hc ω) T
    _ = _ := by simp only [lintegral_const_mul' _ _ (by simp : (T : ℝ≥0∞) ≠ ∞),
      integrandDist, sub_zero]

/-- **Input energy of the ordinary primitive.** Let $P$ be a measure and $H$ a real process indexed
by nonnegative time whose paths are continuous for every sample, and write
$D_t(\omega) = \int_0^t H_s(\omega)\,ds$. For $T \ge 0$,
$$\int_\Omega \int_{(0,T]} |D_t(\omega)|^2\,dt\,dP(\omega) \le
  T^2 \int_\Omega \int_{(0,T]} |H_s(\omega)|^2\,ds\,dP(\omega),$$
where both sides are lower integrals in the extended nonnegative reals: the input energy of the
primitive up to $T$ is at most $T^2$ times that of $H$. -/
theorem integrandDist_timeIntegral_zero_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {H : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous (H · ω)) (T : ℝ≥0) :
    integrandDist P (fun t ω ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal ω) (fun _ _ ↦ 0) T ≤
      (T : ℝ≥0∞)^2 * integrandDist P H (fun _ _ ↦ 0) T := by
  unfold integrandDist
  simp only [sub_zero]
  calc
    _ ≤ ∫⁻ ω, (∫⁻ _s in Ioc (0 : ℝ) T,
        (T : ℝ≥0∞) * ∫⁻ s in Ioc (0 : ℝ) T, ‖H s.toNNReal ω‖ₑ^2) ∂P := by
      apply lintegral_mono
      intro ω
      apply setLIntegral_mono' measurableSet_Ioc
      intro s hs
      have ht : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
      exact (enorm_timeIntegral_sq_le (hc ω) s.toNNReal).trans
        (mul_le_mul' (by exact_mod_cast ht)
          (lintegral_mono_set (Ioc_subset_Ioc_right (by exact_mod_cast ht))))
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
        ENNReal.ofReal_coe_nnreal]
      have he (a : ℝ≥0∞) : (T : ℝ≥0∞) * a * T = (T : ℝ≥0∞)^2 * a := by ring
      simp_rw [he]
      exact lintegral_const_mul' _ _ (by simp : (T : ℝ≥0∞)^2 ≠ ∞)

/-- The actual time integrals of two continuous processes satisfy the squared
integrand-distance bound. No measurability in the sample variable is needed. -/
theorem lintegral_timeIntegral_sub_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X Y : ℝ≥0 → Ω → ℝ} (hX : ∀ ω, Continuous (X · ω))
    (hY : ∀ ω, Continuous (Y · ω)) (t : ℝ≥0) :
    ∫⁻ ω, ‖(∫ s in (0 : ℝ)..t, X s.toNNReal ω) -
      (∫ s in (0 : ℝ)..t, Y s.toNNReal ω)‖ₑ^2 ∂P ≤
        (t : ℝ≥0∞) * integrandDist P X Y t := by
  have h := lintegral_timeIntegral_sq_le P (fun ω ↦ (hX ω).sub (hY ω)) t
  have he (ω : Ω) : (∫ s in (0 : ℝ)..t, X s.toNNReal ω - Y s.toNNReal ω) =
      (∫ s in (0 : ℝ)..t, X s.toNNReal ω) - (∫ s in (0 : ℝ)..t, Y s.toNNReal ω) :=
    intervalIntegral.integral_sub (((hX ω).comp continuous_real_toNNReal).intervalIntegrable _ _)
      (((hY ω).comp continuous_real_toNNReal).intervalIntegrable _ _)
  simpa only [Pi.sub_apply, he, integrandDist, sub_zero] using! h

end ProbabilityTheory
