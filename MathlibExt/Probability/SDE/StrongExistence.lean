/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.SDE.Stability
import MathlibExt.Analysis.ODE.GronwallIntegral
import MathlibExt.Probability.SDE.PicardConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar Lipschitz SDE strong existence and maximal moment bound

The actual Picard iterates converge in mean-square supremum norm. Their input
energy distances therefore vanish, so the actual Itô and ordinary integral
updates converge in L². Uniqueness of limits in measure identifies the continuous
adapted path limit with the actual stochastic integral equation. The solution
uses the prescribed probability measure, Brownian motion and complete filtration.

For any existing solution, subtracting its initial value and ordinary drift gives
a continuous martingale version of its stochastic term. Doob, Lipschitz growth,
and integral Gronwall yield an explicit finite-horizon maximal second-moment
bound. This estimate retains arbitrary filtrations and pre-Brownian laws.

These are the scalar autonomous case of Le Gall, *Brownian Motion, Martingales,
and Stochastic Calculus* (2016), Theorem 8.3, using the complete-filtration
convention in Definition 8.1. The constants are sufficient and nonoptimal.
Completeness is sufficient for existence, not claimed necessary; right continuity
is not required. Pathwise uniqueness is up to one common null set on all times.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

private theorem integrandDist_le_sup_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    integrandDist P X Y T ≤ (T : ℝ≥0∞) *
      ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) T, ‖X s ω - Y s ω‖ₑ) ^ 2 ∂P := by
  unfold integrandDist
  calc
    _ ≤ ∫⁻ ω, (∫⁻ _s in Ioc (0 : ℝ) T,
        (⨆ s : Icc (0 : ℝ≥0) T, ‖X s ω - Y s ω‖ₑ) ^ 2) ∂P := by
      apply lintegral_mono
      intro ω
      apply setLIntegral_mono' measurableSet_Ioc
      intro s hs
      apply pow_le_pow_left₀ zero_le _ 2
      exact le_iSup (fun u : Icc (0 : ℝ≥0) T ↦ ‖X u ω - Y u ω‖ₑ)
        ⟨s.toNNReal, zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
        ENNReal.ofReal_coe_nnreal]
      rw [lintegral_mul_const' _ _ ENNReal.coe_ne_top, mul_comm]


private theorem tendsto_eLpNorm_of_sq_moment
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [NormedAddCommGroup E]
    {f : ℕ → Ω → E} (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (h : Tendsto (fun n ↦ ∫⁻ ω, ‖f n ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (f n) 2 P) atTop (𝓝 0) := by
  have he n : eLpNorm (f n) 2 P = (∫⁻ ω, ‖f n ω‖ₑ ^ 2 ∂P) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) (hf n)]
    norm_num
  simp only [he]
  simpa using h.ennrpow_const (1 / 2)

private theorem tendsto_energy_of_sup_sq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (h : Tendsto (fun n ↦ ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) T,
      ‖X n s ω - Y s ω‖ₑ) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n ↦ integrandDist P (X n) Y T) atTop (𝓝 0) := by
  have hmul := ENNReal.Tendsto.const_mul (a := (T : ℝ≥0∞)) h (Or.inr ENNReal.coe_ne_top)
  rw [mul_zero] at hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
    (fun _ ↦ zero_le) (fun n ↦ integrandDist_le_sup_sq P (X n) Y T)


private theorem solution_of_picard_convergence
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    (x : ℝ) (X : ℕ → ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ)
    (hX : ∀ n, IsProgressive F (X n) ∧ (∀ ω, Continuous (X n · ω)) ∧
      ∀ T, integrandDist P (X n) (fun _ _ ↦ 0) T ≠ ∞)
    (heq : ∀ n t, X (n + 1) t =ᵐ[P] fun ω ↦
      x + itoIntegral P F B (fun s ω ↦ σ (X n s ω)) t ω +
        ∫ s in (0 : ℝ)..t, b (X n s.toNNReal ω))
    (hYp : IsProgressive F Y) (hYc : ∀ ω, Continuous (Y · ω))
    (hU : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      TendstoUniformlyOn (fun n s ↦ X n s ω) (Y · ω) atTop (Icc 0 T))
    (hL : ∀ T : ℝ≥0,
      (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) T, ‖Y s ω‖ₑ) ^ 2 ∂P) ≠ ∞ ∧
      Tendsto (fun n ↦ ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) T,
        ‖X n s ω - Y s ω‖ₑ) ^ 2 ∂P) atTop (𝓝 0)) :
    IsScalarSDESolution P F B σ b x Y := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hYe (T : ℝ≥0) : integrandDist P Y (fun _ _ ↦ 0) T ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (hL T).1)
    simpa only [sub_zero] using integrandDist_le_sup_sq P Y (fun _ _ ↦ 0) T
  refine ⟨hYp.adapted, hYc, hYe, ?_⟩
  intro t
  have he := tendsto_energy_of_sup_sq P X Y t (hL t).2
  let I (n : ℕ) := itoIntegral P F B (fun s ω ↦ σ (X n s ω)) t
  let Q := itoIntegral P F B (fun s ω ↦ σ (Y s ω)) t
  let D (n : ℕ) (ω : Ω) := ∫ s in (0 : ℝ)..t, b (X n s.toNNReal ω)
  let R (ω : Ω) := ∫ s in (0 : ℝ)..t, b (Y s.toNNReal ω)
  have hIm (n : ℕ) : AEStronglyMeasurable (I n - Q) P :=
    ((memLp_itoIntegral P F B (fun s ω ↦ σ (X n s ω)) t).sub
      (memLp_itoIntegral P F B (fun s ω ↦ σ (Y s ω)) t)).aestronglyMeasurable
  have hDm (n : ℕ) : AEStronglyMeasurable (D n - R) P := by
    have hn := memLp_timeIntegral
      (show IsProgressive F (fun s ω ↦ b (X n s ω)) from
        fun T ↦ hb.continuous.measurable.comp ((hX n).1 T))
      (fun ω ↦ hb.continuous.comp ((hX n).2.1 ω)) t
      (integrandDist_comp_zero_ne_top (hX n).1 hb t ((hX n).2.2 t))
    have hy := memLp_timeIntegral
      (show IsProgressive F (fun s ω ↦ b (Y s ω)) from
        fun T ↦ hb.continuous.measurable.comp (hYp T))
      (fun ω ↦ hb.continuous.comp (hYc ω)) t
      (integrandDist_comp_zero_ne_top hYp hb t (hYe t))
    exact (hn.sub hy).aestronglyMeasurable
  have hi : Tendsto (fun n ↦ eLpNorm (I n - Q) 2 P) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_of_sq_moment hIm
    have hm := ENNReal.Tendsto.const_mul (a := (K : ℝ≥0∞) ^ 2) he
      (Or.inr (by finiteness))
    rw [mul_zero] at hm
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm (fun _ ↦ zero_le)
    intro n
    exact lintegral_itoIntegral_sub_comp_lipschitz_le hB hBF hInd (hX n).1 hYp hσ t
      ((hX n).2.2 t) (hYe t)
  have hd : Tendsto (fun n ↦ eLpNorm (D n - R) 2 P) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_of_sq_moment hDm
    have hm := ENNReal.Tendsto.const_mul (a := (t : ℝ≥0∞) * (K : ℝ≥0∞) ^ 2) he
      (Or.inr (by finiteness))
    rw [mul_zero] at hm
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm (fun _ ↦ zero_le)
    intro n
    calc
      _ ≤ (t : ℝ≥0∞) * integrandDist P (fun s ω ↦ b (X n s ω)) (fun s ω ↦ b (Y s ω)) t :=
        lintegral_timeIntegral_sub_sq_le P
          (fun ω ↦ hb.continuous.comp ((hX n).2.1 ω))
          (fun ω ↦ hb.continuous.comp (hYc ω)) t
      _ ≤ _ := by
        dsimp only
        rw [mul_assoc]
        exact mul_le_mul' le_rfl (integrandDist_comp_lipschitz_le hb P (X n) Y t)
  let U (n : ℕ) (ω : Ω) := x + I n ω + D n ω
  let V (ω : Ω) := x + Q ω + R ω
  have hr : TendstoInMeasure P U atTop V := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    have hm := hi.add hd
    rw [add_zero] at hm
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm (fun _ ↦ zero_le)
    intro n
    have he : U n - V = (I n - Q) + (D n - R) := by funext ω; dsimp [U, V]; ring
    dsimp only
    rw [he]
    exact eLpNorm_add_le (by norm_num)
  have hx : TendstoInMeasure P (fun n ↦ X (n + 1) t) atTop (Y t) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun n ↦ ((hX (n + 1)).1.adapted.measurable).aestronglyMeasurable)
    filter_upwards [hU] with ω hω
    exact ((hω t).tendsto_at ⟨zero_le, le_rfl⟩).comp (tendsto_add_atTop_nat 1)
  have hr' : TendstoInMeasure P (fun n ↦ X (n + 1) t) atTop V :=
    TendstoInMeasure.congr_left (fun n ↦ (heq n t).symm) hr
  exact tendstoInMeasure_ae_unique hx hr'


private theorem solution_martingale_decomposition
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B Y : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} {x : ℝ} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    (hY : IsScalarSDESolution P F B σ b x Y) :
    ∃ J : ℝ≥0 → Ω → ℝ, Martingale J F P ∧ IsProgressive F J ∧
      (∀ ω, Continuous (J · ω)) ∧
      (∀ t, J t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (Y s ω)) t) ∧
      ∀ t ω, Y t ω = x + J t ω + ∫ s in (0 : ℝ)..t, b (Y s.toNNReal ω) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hbp : IsProgressive F (fun s ω ↦ b (Y s ω)) :=
    fun T ↦ hb.continuous.measurable.comp (hY.isProgressive T)
  have hbc : ∀ ω, Continuous (fun s ↦ b (Y s ω)) :=
    fun ω ↦ hb.continuous.comp (hY.2.1 ω)
  let D (t : ℝ≥0) (ω : Ω) := ∫ s in (0 : ℝ)..t, b (Y s.toNNReal ω)
  have hDp : IsProgressive F D := IsProgressive.timeIntegral hbp hbc
  have hDc ω : Continuous (D · ω) := continuous_timeIntegral (hbc ω)
  let J (t : ℝ≥0) (ω : Ω) := Y t ω - x - D t ω
  have hJp : IsProgressive F J := fun T ↦ ((hY.isProgressive T).sub measurable_const).sub (hDp T)
  have hJc ω : Continuous (J · ω) := ((hY.2.1 ω).sub continuous_const).sub (hDc ω)
  have he t : J t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (Y s ω)) t := by
    filter_upwards [hY.2.2.2 t] with ω hω
    dsimp only [J, D]
    linarith
  have hm := martingale_itoIntegral_of_isProgressive hB hBF hInd
    (show IsProgressive F (fun s ω ↦ σ (Y s ω)) from
      fun T ↦ hσ.continuous.measurable.comp (hY.isProgressive T))
    (fun T ↦ by simpa only [integrandDist, sub_zero] using
      integrandDist_comp_zero_ne_top hY.isProgressive hσ T (hY.2.2.1 T))
  refine ⟨J, hm.congr hJp.adapted.stronglyAdapted (fun t ↦ (he t).symm), hJp, hJc, he, ?_⟩
  intro t ω
  dsimp only [J, D]
  ring

private theorem energy_comp_growth_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : IsProgressive F X)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ≥0) :
    integrandDist P (fun s ω ↦ f (X s ω)) (fun _ _ ↦ 0) t ≤
      2 * (K : ℝ≥0∞) ^ 2 * integrandDist P X (fun _ _ ↦ 0) t + 2 * ‖f 0‖ₑ ^ 2 * t := by
  have h := integrandDist_le (P := P) (X := fun s ω ↦ f (X s ω)) (Y := fun _ _ ↦ 0)
    (Z := fun _ _ ↦ f 0)
    (hf.continuous.measurable.comp (IsProgressive.measurable_toNNReal hX))
    measurable_const measurable_const t
  have hc : integrandDist P (fun _ _ ↦ 0) (fun _ _ ↦ f 0) t = ‖f 0‖ₑ ^ 2 * t := by
    simp [integrandDist, Real.volume_Ioc]
  calc
    _ ≤ 2 * integrandDist P (fun s ω ↦ f (X s ω)) (fun _ _ ↦ f 0) t +
        2 * integrandDist P (fun _ _ ↦ 0) (fun _ _ ↦ f 0) t := h
    _ ≤ 2 * ((K : ℝ≥0∞) ^ 2 * integrandDist P X (fun _ _ ↦ 0) t) +
        2 * (‖f 0‖ₑ ^ 2 * t) := by
      rw [hc]
      exact add_le_add (mul_le_mul' le_rfl (integrandDist_comp_lipschitz_le hf P X
        (fun _ _ ↦ 0) t)) le_rfl
    _ = _ := by ring

private theorem sup_moment_measurable {Ω : Type*} [MeasurableSpace Ω]
    {H : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (H t))
    (hc : ∀ ω, Continuous (H · ω)) (T : ℝ≥0) :
    Measurable fun ω ↦ (⨆ s : Icc (0 : ℝ≥0) T, ‖H s ω‖ₑ) ^ 2 := by
  let Z : Ω → C(Icc (0 : ℝ≥0) T, ℝ) :=
    fun ω ↦ ⟨fun s ↦ H s ω, (hc ω).comp continuous_subtype_val⟩
  have hz : Measurable Z := ContinuousMap.measurable_iff_eval.2 (fun s ↦ hm s)
  simpa only [ContinuousMap.eNorm_eq_iSup_eNorm, Z, ContinuousMap.coe_mk] using hz.eNorm.pow_const 2

private theorem lintegral_sup_three_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : ℝ) (J D : ℝ≥0 → Ω → ℝ)
    (hJm : ∀ t, Measurable (J t)) (hJc : ∀ ω, Continuous (J · ω)) (t : ℝ≥0) :
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖x + J s ω + D s ω‖ₑ) ^ 2 ∂P ≤
      3 * (‖x‖ₑ ^ 2 + (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖J s ω‖ₑ) ^ 2 ∂P) +
        ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖D s ω‖ₑ) ^ 2 ∂P) := by
  let : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, zero_le⟩⟩
  have hp (a b c : ℝ) : ‖a + b + c‖ₑ ^ 2 ≤ 3 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2 + ‖c‖ₑ ^ 2) := by
    have h : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have he := ENNReal.ofReal_le_ofReal h
    simpa only [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
      ENNReal.ofReal_mul (by norm_num : 0 ≤ (3 : ℝ)), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_add (add_nonneg (sq_nonneg a) (sq_nonneg b)) (sq_nonneg c),
      ENNReal.ofReal_add (sq_nonneg a) (sq_nonneg b)] using he
  calc
    _ ≤ ∫⁻ ω, 3 * (‖x‖ₑ ^ 2 + (⨆ s : Icc (0 : ℝ≥0) t, ‖J s ω‖ₑ) ^ 2 +
        (⨆ s : Icc (0 : ℝ≥0) t, ‖D s ω‖ₑ) ^ 2) ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [ENNReal.iSup_pow]
      apply iSup_le
      intro s
      exact (hp x (J s ω) (D s ω)).trans (mul_le_mul' le_rfl (add_le_add
        (add_le_add le_rfl (pow_le_pow_left₀ zero_le (le_iSup
          (fun r : Icc (0 : ℝ≥0) t ↦ ‖J r ω‖ₑ) s) 2))
        (pow_le_pow_left₀ zero_le (le_iSup (fun r : Icc (0 : ℝ≥0) t ↦ ‖D r ω‖ₑ) s) 2)))
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ∞)]
      rw [lintegral_add_left' (show AEMeasurable
        (fun ω ↦ ‖x‖ₑ ^ 2 + (⨆ s : Icc (0 : ℝ≥0) t, ‖J s ω‖ₑ) ^ 2) P from
        aemeasurable_const.add (sup_moment_measurable hJm hJc t).aemeasurable),
        lintegral_add_left' (f := fun _ : Ω ↦ ‖x‖ₑ ^ 2) aemeasurable_const]
      simp


private theorem sup_moment_le_energy
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B Y : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} {x : ℝ}
    (hY : IsScalarSDESolution P F B σ b x Y) (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    (t : ℝ≥0) :
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖Y s ω‖ₑ) ^ 2 ∂P ≤
      3 * (‖x‖ₑ ^ 2 + 4 * integrandDist P (fun s ω ↦ σ (Y s ω)) (fun _ _ ↦ 0) t +
        (t : ℝ≥0∞) * integrandDist P (fun s ω ↦ b (Y s ω)) (fun _ _ ↦ 0) t) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨J, hJm, hJp, hJc, hJe, hEq⟩ := solution_martingale_decomposition hB hBF hInd hσ hb hY
  let D (s : ℝ≥0) (ω : Ω) := ∫ u in (0 : ℝ)..s, b (Y u.toNNReal ω)
  have hA := lintegral_iSup_ito_version_sq_le hB hBF hInd
    (show IsProgressive F (fun s ω ↦ σ (Y s ω)) from
      fun T ↦ hσ.continuous.measurable.comp (hY.isProgressive T)) hJm hJc hJe t
    (integrandDist_comp_zero_ne_top hY.isProgressive hσ t (hY.2.2.1 t))
  have hD := lintegral_iSup_timeIntegral_sq_le P
    (fun ω ↦ hb.continuous.comp (hY.2.1 ω)) t
  have hthree := lintegral_sup_three_sq_le P x J D (fun s ↦ hJp.adapted.measurable) hJc t
  calc
    _ ≤ 3 * (‖x‖ₑ ^ 2 + (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖J s ω‖ₑ) ^ 2 ∂P) +
        ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖D s ω‖ₑ) ^ 2 ∂P) := by
      have he : (fun ω ↦ (⨆ s : Icc (0 : ℝ≥0) t, ‖Y s ω‖ₑ) ^ 2) =
          (fun ω ↦ (⨆ s : Icc (0 : ℝ≥0) t, ‖x + J s ω + D s ω‖ₑ) ^ 2) := by
        funext ω
        exact congrArg (fun z : ℝ≥0∞ ↦ z ^ 2) (iSup_congr fun s ↦ congrArg
          (fun z : ℝ ↦ ‖z‖ₑ) (hEq s ω))
      rw [he]
      exact hthree
    _ ≤ _ := mul_le_mul' le_rfl (add_le_add (add_le_add le_rfl hA) (by
      calc
        _ ≤ ∫⁻ ω, ⨆ (s : ℝ≥0) (_ : s ≤ t), ‖D s ω‖ₑ ^ 2 ∂P := by
          apply lintegral_mono
          intro ω
          dsimp only
          let : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, zero_le⟩⟩
          rw [ENNReal.iSup_pow]
          exact iSup_le fun s ↦ le_iSup_of_le (s : ℝ≥0) (le_iSup_of_le s.property.2 le_rfl)
        _ ≤ _ := by simpa only [D, integrandDist, sub_zero, Function.comp_apply] using hD))

private theorem sup_moment_finite
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B Y : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} {x : ℝ}
    (hY : IsScalarSDESolution P F B σ b x Y) (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    (t : ℝ≥0) :
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖Y s ω‖ₑ) ^ 2 ∂P) ≠ ∞ := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hs := integrandDist_comp_zero_ne_top hY.isProgressive hσ t (hY.2.2.1 t)
  have hb' := integrandDist_comp_zero_ne_top hY.isProgressive hb t (hY.2.2.1 t)
  exact ne_top_of_le_ne_top (by finiteness) (sup_moment_le_energy hB hBF hInd hY hσ hb t)

private theorem sup_moment_le_add_energy
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B Y : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} {x : ℝ}
    (hY : IsScalarSDESolution P F B σ b x Y) (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    {t T : ℝ≥0} (ht : t ≤ T) :
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖Y s ω‖ₑ) ^ 2 ∂P ≤
      3 * ‖x‖ₑ ^ 2 + (24 * ‖σ 0‖ₑ ^ 2 + 6 * (T : ℝ≥0∞) * ‖b 0‖ₑ ^ 2) * T +
        ((24 + 6 * (T : ℝ≥0∞)) * (K : ℝ≥0∞) ^ 2) * integrandDist P Y (fun _ _ ↦ 0) t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hs := energy_comp_growth_le (P := P) hY.isProgressive hσ t
  have hd := energy_comp_growth_le (P := P) hY.isProgressive hb t
  have htE : (t : ℝ≥0∞) ≤ T := by exact_mod_cast ht
  calc
    _ ≤ 3 * (‖x‖ₑ ^ 2 + 4 * integrandDist P (fun s ω ↦ σ (Y s ω)) (fun _ _ ↦ 0) t +
        (t : ℝ≥0∞) * integrandDist P (fun s ω ↦ b (Y s ω)) (fun _ _ ↦ 0) t) :=
      sup_moment_le_energy hB hBF hInd hY hσ hb t
    _ ≤ 3 * (‖x‖ₑ ^ 2 + 4 * (2 * (K : ℝ≥0∞) ^ 2 * integrandDist P Y (fun _ _ ↦ 0) t +
        2 * ‖σ 0‖ₑ ^ 2 * t) + (t : ℝ≥0∞) * (2 * (K : ℝ≥0∞) ^ 2 *
        integrandDist P Y (fun _ _ ↦ 0) t + 2 * ‖b 0‖ₑ ^ 2 * t)) := by
      exact mul_le_mul' le_rfl (add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hs))
        (mul_le_mul' le_rfl hd))
    _ ≤ 3 * (‖x‖ₑ ^ 2 + 4 * (2 * (K : ℝ≥0∞) ^ 2 * integrandDist P Y (fun _ _ ↦ 0) t +
        2 * ‖σ 0‖ₑ ^ 2 * T) + (T : ℝ≥0∞) * (2 * (K : ℝ≥0∞) ^ 2 *
        integrandDist P Y (fun _ _ ↦ 0) t + 2 * ‖b 0‖ₑ ^ 2 * T)) := by gcongr
    _ = _ := by ring


private theorem sup_moment_monotone {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℝ≥0 → Ω → ℝ) :
    Monotone (fun t : ℝ≥0 ↦ ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖Y s ω‖ₑ) ^ 2 ∂P) := by
  intro t T ht
  apply lintegral_mono
  intro ω
  apply pow_le_pow_left₀ zero_le _ 2
  apply iSup_le
  intro s
  exact le_iSup_of_le (⟨s, s.property.1, s.property.2.trans ht⟩ : Icc (0 : ℝ≥0) T) le_rfl

private theorem energy_toReal_le_integral_sup
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {Y : ℝ≥0 → Ω → ℝ} (hY : IsProgressive F Y)
    (hfin : ∀ t : ℝ≥0, (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖Y s ω‖ₑ) ^ 2 ∂P) ≠ ∞)
    (t : ℝ≥0) :
    (integrandDist P Y (fun _ _ ↦ 0) t).toReal ≤
      ∫ s in (0 : ℝ)..t, (∫⁻ ω,
        (⨆ u : Icc (0 : ℝ≥0) s.toNNReal, ‖Y u ω‖ₑ) ^ 2 ∂P).toReal := by
  let u (s : ℝ) := (∫⁻ ω, (⨆ v : Icc (0 : ℝ≥0) s.toNNReal, ‖Y v ω‖ₑ) ^ 2 ∂P).toReal
  have hmono : Monotone u := fun a b hab ↦ ENNReal.toReal_mono (hfin _)
    (sup_moment_monotone P Y (Real.toNNReal_le_toNNReal hab))
  have hu : IntervalIntegrable u volume (0 : ℝ) t :=
    ((hmono.monotoneOn _).integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hm : Measurable fun p : Ω × ℝ ↦ ‖Y p.2.toNNReal p.1‖ₑ ^ 2 :=
    ((IsProgressive.measurable_toNNReal hY).comp measurable_swap).eNorm.pow_const 2
  have he : integrandDist P Y (fun _ _ ↦ 0) t ≤ ENNReal.ofReal (∫ s in (0 : ℝ)..t, u s) := by
    simp only [integrandDist, sub_zero]
    rw [lintegral_lintegral_swap hm.aemeasurable]
    calc
      _ ≤ ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (u s) := by
        apply lintegral_mono
        intro s
        dsimp only [u]
        rw [ENNReal.ofReal_toReal (hfin _)]
        apply lintegral_mono
        intro ω
        exact pow_le_pow_left₀ zero_le (le_iSup
          (fun v : Icc (0 : ℝ≥0) s.toNNReal ↦ ‖Y v ω‖ₑ)
          ⟨s.toNNReal, zero_le, le_rfl⟩) 2
      _ = _ := by
        rw [intervalIntegral.integral_of_le t.coe_nonneg]
        exact (ofReal_integral_eq_lintegral_ofReal hu.1
          (Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)).symm
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg t.coe_nonneg
    (fun _ _ ↦ ENNReal.toReal_nonneg)), u] using h


/-- A scalar Lipschitz SDE solution has the explicit finite-horizon supremum
second-moment bound. Finiteness is derived before Gronwall. Only pre-Brownian laws
and the given arbitrary filtration are needed: the solution minus its initial
value and ordinary drift is already a continuous martingale version. -/
theorem IsScalarSDESolution.lintegral_iSup_sq_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B Y : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} {x : ℝ}
    (hY : IsScalarSDESolution P F B σ b x Y) (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    {t T : ℝ≥0} (ht : t ≤ T) :
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖Y s ω‖ₑ) ^ 2 ∂P ≤
      ENNReal.ofReal ((3 * x ^ 2 + (24 * (σ 0) ^ 2 + 6 * (T : ℝ) * (b 0) ^ 2) * T) *
        Real.exp ((24 + 6 * (T : ℝ)) * (K : ℝ) ^ 2 * t)) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  let u (s : ℝ) := (∫⁻ ω, (⨆ v : Icc (0 : ℝ≥0) s.toNNReal, ‖Y v ω‖ₑ) ^ 2 ∂P).toReal
  have hfin := sup_moment_finite hB hBF hInd hY hσ hb
  have hmono : Monotone u := fun a b hab ↦ ENNReal.toReal_mono (hfin _)
    (sup_moment_monotone P Y (Real.toNNReal_le_toNNReal hab))
  have hint : IntegrableOn u (Icc (0 : ℝ) T) :=
    (hmono.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hineq : ∀ s ∈ Icc (0 : ℝ) T,
      u s ≤ 3 * x ^ 2 + (24 * (σ 0) ^ 2 + 6 * (T : ℝ) * (b 0) ^ 2) * T +
        ((24 + 6 * (T : ℝ)) * (K : ℝ) ^ 2) * ∫ r in (0 : ℝ)..s, u r := by
    intro s hs
    have hst : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
    have h := sup_moment_le_add_energy hB hBF hInd hY hσ hb hst
    have hE := hY.2.2.1 s.toNNReal
    have hr := ENNReal.toReal_mono (by finiteness) h
    have hfinite1 : (3 * ‖x‖ₑ ^ 2 : ℝ≥0∞) ≠ ∞ := by finiteness
    have hfinite2 : ((24 * ‖σ 0‖ₑ ^ 2 + 6 * (T : ℝ≥0∞) * ‖b 0‖ₑ ^ 2) * T) ≠ ∞ := by finiteness
    have hfinite3 : (((24 + 6 * (T : ℝ≥0∞)) * (K : ℝ≥0∞) ^ 2) *
      integrandDist P Y (fun _ _ ↦ 0) s.toNNReal) ≠ ∞ := by finiteness
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfinite1, hfinite2⟩) hfinite3,
      ENNReal.toReal_add hfinite1 hfinite2] at hr
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, Real.eNorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), sq_abs,
      ENNReal.toReal_add (by finiteness : (24 * ENNReal.ofReal |σ 0| ^ 2) ≠ ∞)
        (by finiteness : (6 * (T : ℝ≥0∞) * ENNReal.ofReal |b 0| ^ 2) ≠ ∞),
      ENNReal.toReal_add (by norm_num : (24 : ℝ≥0∞) ≠ ∞)
        (by finiteness : 6 * (T : ℝ≥0∞) ≠ ∞)] at hr
    have he := energy_toReal_le_integral_sup hY.isProgressive hfin s.toNNReal
    have hm := mul_le_mul_of_nonneg_left he
      (by positivity : 0 ≤ (24 + 6 * (T : ℝ)) * (K : ℝ) ^ 2)
    have hsum := hr.trans (add_le_add le_rfl hm)
    simpa only [u, Real.coe_toNNReal s hs.1, Real.toNNReal_coe, Real.eNorm_eq_ofReal_abs] using hsum
  have hg := MathlibExt.Analysis.ODE.le_mul_exp_of_le_add_integral
    (by positivity : 0 ≤ (24 + 6 * (T : ℝ)) * (K : ℝ) ^ 2) hint
    (fun _ _ ↦ ENNReal.toReal_nonneg) hineq (t : ℝ) ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have he := ENNReal.ofReal_le_ofReal hg
  have heq : ENNReal.ofReal (u t) =
      ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖Y s ω‖ₑ) ^ 2 ∂P := by
    dsimp only [u]
    rw [show (t : ℝ).toNNReal = t from Real.toNNReal_coe]
    exact ENNReal.ofReal_toReal (hfin t)
  rw [heq] at he
  simpa only [mul_assoc] using he


/-- Strong existence and pathwise uniqueness for a scalar autonomous globally
Lipschitz SDE on the prescribed complete filtration and Brownian probability
space. The solution has continuous paths for every sample, locally finite energy,
the actual Itô-plus-drift equation, and an explicit supremum second-moment bound.
Uniqueness is up to indistinguishability on all nonnegative times. No right
continuity of the filtration or pre-existing solution is assumed. -/
theorem exists_unique_scalar_sde_solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b) (x : ℝ) :
    ∃ Y : ℝ≥0 → Ω → ℝ, IsScalarSDESolution P F B σ b x Y ∧
      (∀ t T : ℝ≥0, t ≤ T →
        ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖Y s ω‖ₑ) ^ 2 ∂P ≤
          ENNReal.ofReal ((3 * x ^ 2 + (24 * (σ 0) ^ 2 + 6 * (T : ℝ) * (b 0) ^ 2) * T) *
            Real.exp ((24 + 6 * (T : ℝ)) * (K : ℝ) ^ 2 * t))) ∧
      ∀ Z, IsScalarSDESolution P F B σ b x Z → Y ≡ᵐ[P] Z := by
  obtain ⟨X, J, h0, hX, hJ⟩ := exists_scalar_sde_picard_sequence hB hBF hInd hσ hb x
  obtain ⟨Y, hYp, hYc, hU, hL⟩ := exists_scalar_sde_picard_limit hB.toIsPreBrownianReal
    hBF hInd hσ hb x X J h0 hX hJ
  have heq (n : ℕ) (t : ℝ≥0) : X (n + 1) t =ᵐ[P] fun ω ↦
      x + itoIntegral P F B (fun s ω ↦ σ (X n s ω)) t ω +
        ∫ s in (0 : ℝ)..t, b (X n s.toNNReal ω) := by
    filter_upwards [(hJ n).2.2.2.1 t] with ω hω
    rw [(hJ n).2.2.2.2]
    dsimp only
    rw [hω]
  have hY := solution_of_picard_convergence hB.toIsPreBrownianReal hBF hInd hσ hb x X Y
    hX heq hYp hYc hU hL
  exact ⟨Y, hY, fun _ _ ht ↦ IsScalarSDESolution.lintegral_iSup_sq_le
    hB.toIsPreBrownianReal hBF hInd hY hσ hb ht, fun Z hZ ↦
      hY.indistinguishable hB.toIsPreBrownianReal hBF hInd hZ hσ hb⟩

end ProbabilityTheory
