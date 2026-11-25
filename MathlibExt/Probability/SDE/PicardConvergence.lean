/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.SDE.PicardIteration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Convergence of scalar SDE Picard iteration

Iterating the maximal second-moment bound gives a factorial bound for successive
Picard increments. Its square roots are summable. In the Banach space of continuous
paths on a compact interval, summable L² increments yield almost-sure uniform
convergence and L² convergence to the same limit. A countable intersection over
integer horizons gives one all-time process. A common null-set fallback preserves
adaptedness under the explicit complete-filtration hypothesis.

This is the convergence argument in Le Gall, *Brownian Motion, Martingales, and
Stochastic Calculus* (2016), Theorem 8.3, with the filtration convention of
Definition 8.1. The factorial estimate itself needs only pre-Brownian laws and
an arbitrary filtration. Completeness is sufficient for the limit construction;
right continuity is not required. No convergence or solution is assumed.
The limiting integral equation is a separate step.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

private theorem energy_le_integral_envelope {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X Y : ℝ≥0 → Ω → ℝ} (hXp : IsProgressive F X) (hYp : IsProgressive F Y)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Continuous f)
    (hn : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ f s)
    (hb : ∀ s : ℝ≥0, s ≤ t → ∫⁻ ω, ‖X s ω - Y s ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (f s)) :
    integrandDist P X Y t ≤ ENNReal.ofReal (∫ s in (0 : ℝ)..t, f s) := by
  have hm : Measurable fun p : Ω × ℝ ↦ ‖X p.2.toNNReal p.1 - Y p.2.toNNReal p.1‖ₑ ^ 2 :=
    (((IsProgressive.measurable_toNNReal hXp).sub
      (IsProgressive.measurable_toNNReal hYp)).comp measurable_swap).eNorm.pow_const 2
  rw [integrandDist, lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (f s) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro s hs
      have h := hb s.toNNReal (Real.toNNReal_le_iff_le_coe.2 hs.2)
      simpa only [Real.coe_toNNReal s hs.1.le] using h
    _ = _ := by
      rw [intervalIntegral.integral_of_le t.coe_nonneg]
      symm
      apply ofReal_integral_eq_lintegral_ofReal (hf.intervalIntegrable 0 t).1
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hn s ⟨hs.1.le, hs.2⟩

private theorem energy_le_integral_sup_envelope {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X Y : ℝ≥0 → Ω → ℝ} (hXp : IsProgressive F X) (hYp : IsProgressive F Y)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Continuous f)
    (hn : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ f s)
    (hb : ∀ s : ℝ≥0, s ≤ t →
      ∫⁻ ω, (⨆ u : Icc (0 : ℝ≥0) s, ‖X u ω - Y u ω‖ₑ) ^ 2 ∂P ≤ ENNReal.ofReal (f s)) :
    integrandDist P X Y t ≤ ENNReal.ofReal (∫ s in (0 : ℝ)..t, f s) := by
  apply energy_le_integral_envelope hXp hYp t hf hn
  intro s hs
  refine (lintegral_mono fun ω ↦ ?_).trans (hb s hs)
  exact pow_le_pow_left₀ zero_le
    (le_iSup (fun u : Icc (0 : ℝ≥0) s ↦ ‖X u ω - Y u ω‖ₑ) ⟨s, zero_le, le_rfl⟩) 2

private theorem integral_picard_envelope (C A t : ℝ) (n : ℕ) :
    A * (∫ s in (0 : ℝ)..t, C * A ^ n * s ^ (n + 1) / (n + 1).factorial) =
      C * A ^ (n + 1) * t ^ (n + 2) / (n + 2).factorial := by
  have he : (fun s : ℝ ↦ C * A ^ n * s ^ (n + 1) / (n + 1).factorial) =
      (fun s ↦ (C * A ^ n / (n + 1).factorial) * s ^ (n + 1)) := by
    funext s
    ring
  rw [he, intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : n + 1 + 1 ≠ 0), sub_zero]
  rw [show (n + 2).factorial = (n + 2) * (n + 1).factorial from
    Nat.factorial_succ (n + 1), pow_succ A]
  push_cast
  have hn : ((n + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem ofReal_initial_coefficient (a c : ℝ) (T : ℝ≥0) :
    ENNReal.ofReal (8 * a ^ 2 + 2 * (T : ℝ) * c ^ 2) =
      8 * ‖a‖ₑ ^ 2 + 2 * (T : ℝ≥0∞) * ‖c‖ₑ ^ 2 := by
  simp only [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (8 : ℝ)),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (T : ℝ)),
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
  simp

private theorem ofReal_iteration_coefficient (K T : ℝ≥0) :
    ENNReal.ofReal (2 * (4 + (T : ℝ)) * (K : ℝ) ^ 2) =
      2 * (4 + (T : ℝ≥0∞)) * (K : ℝ≥0∞) ^ 2 := by
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (4 + (T : ℝ))),
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
    ENNReal.ofReal_add (by norm_num : 0 ≤ (4 : ℝ)) T.coe_nonneg,
    ENNReal.ofReal_pow K.coe_nonneg]
  simp

/-- Successive actual Picard iterates satisfy a factorial maximal second-moment
bound on every bounded time interval. The bound includes zero time and zero
Lipschitz constant. It uses pre-Brownian laws and arbitrary filtrations; no
convergence assumption or completeness is needed for this estimate. -/
theorem lintegral_iSup_picard_succ_sub_sq_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    (x : ℝ) (X J : ℕ → ℝ≥0 → Ω → ℝ) (h0 : X 0 = fun _ _ ↦ x)
    (hX : ∀ n, IsProgressive F (X n) ∧ (∀ ω, Continuous (X n · ω)) ∧
      ∀ T, integrandDist P (X n) (fun _ _ ↦ 0) T ≠ ∞)
    (hJ : ∀ n, Martingale (J n) F P ∧ IsProgressive F (J n) ∧
      (∀ ω, Continuous (J n · ω)) ∧
      (∀ t, J n t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (X n s ω)) t) ∧
      X (n + 1) = fun t ω ↦ x + J n t ω + ∫ s in (0 : ℝ)..t, b (X n s.toNNReal ω))
    (T : ℝ≥0) : ∀ (n : ℕ) (t : ℝ≥0), t ≤ T →
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖X (n + 1) s ω - X n s ω‖ₑ) ^ 2 ∂P ≤
      ENNReal.ofReal ((8 * (σ x) ^ 2 + 2 * (T : ℝ) * (b x) ^ 2) *
        (2 * (4 + (T : ℝ)) * (K : ℝ) ^ 2) ^ n * (t : ℝ) ^ (n + 1) / (n + 1).factorial) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  let C : ℝ := 8 * (σ x) ^ 2 + 2 * (T : ℝ) * (b x) ^ 2
  let A : ℝ := 2 * (4 + (T : ℝ)) * (K : ℝ) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  change ∀ (n : ℕ) (t : ℝ≥0), t ≤ T →
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖X (n + 1) s ω - X n s ω‖ₑ) ^ 2 ∂P ≤
      ENNReal.ofReal (C * A ^ n * (t : ℝ) ^ (n + 1) / (n + 1).factorial)
  intro n
  induction n with
  | zero =>
    intro t ht
    have heJ (u) : J 0 u =ᵐ[P] itoIntegral P F B (fun _ _ ↦ σ x) u := by
      simpa only [h0] using (hJ 0).2.2.2.1 u
    have hi := lintegral_iSup_ito_const_add_drift_sq_le hB hBF hInd
      (σ x) (b x) (hJ 0).1 (hJ 0).2.2.1 heJ t
    have he (s : Icc (0 : ℝ≥0) t) (ω : Ω) :
        X (0 + 1) s ω - X 0 s ω = J 0 s ω + (s : ℝ) * b x := by
      rw [(hJ 0).2.2.2.2, h0]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      ring
    simp only [he, pow_zero, mul_one, zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    calc
      _ ≤ (8 * ‖σ x‖ₑ ^ 2 + 2 * (t : ℝ≥0∞) * ‖b x‖ₑ ^ 2) * (t : ℝ≥0∞) := hi
      _ ≤ (8 * ‖σ x‖ₑ ^ 2 + 2 * (T : ℝ≥0∞) * ‖b x‖ₑ ^ 2) * (t : ℝ≥0∞) := by
        have htE : (t : ℝ≥0∞) ≤ T := by exact_mod_cast ht
        exact mul_le_mul' (add_le_add le_rfl
          (mul_le_mul' (mul_le_mul' le_rfl htE) le_rfl)) le_rfl
      _ = _ := by
        rw [ENNReal.ofReal_mul hC, ofReal_initial_coefficient, ENNReal.ofReal_coe_nnreal]
  | succ n ih =>
    intro t ht
    have hu := lintegral_iSup_picard_sub_le hB hBF hInd hσ hb
      (hX (n + 1)).1 (hX n).1 (hX (n + 1)).2.1 (hX n).2.1
      (hJ (n + 1)).1 (hJ n).1 (hJ (n + 1)).2.2.1 (hJ n).2.2.1
      (hJ (n + 1)).2.2.2.1 (hJ n).2.2.2.1 x t
      ((hX (n + 1)).2.2 t) ((hX n).2.2 t)
    have he (s : Icc (0 : ℝ≥0) t) (ω : Ω) :
        X (n + 1 + 1) s ω - X (n + 1) s ω =
        (x + J (n + 1) s ω + ∫ u in (0 : ℝ)..s, b (X (n + 1) u.toNNReal ω)) -
        (x + J n s ω + ∫ u in (0 : ℝ)..s, b (X n u.toNNReal ω)) := by
      exact congrArg₂ (· - ·)
        (congrFun (congrFun (hJ (n + 1)).2.2.2.2 s) ω)
        (congrFun (congrFun (hJ n).2.2.2.2 s) ω)
    have henergy := energy_le_integral_sup_envelope (hX (n + 1)).1 (hX n).1 t
      (f := fun s ↦ C * A ^ n * s ^ (n + 1) / (n + 1).factorial)
      (by fun_prop) (fun s hs ↦ by have hs0 := hs.1; positivity)
      (fun s hs ↦ ih s (hs.trans ht))
    calc
      _ ≤ 2 * (4 + (t : ℝ≥0∞)) * (K : ℝ≥0∞) ^ 2 *
          integrandDist P (X (n + 1)) (X n) t := by simpa only [he] using hu
      _ ≤ ENNReal.ofReal A * integrandDist P (X (n + 1)) (X n) t := by
        rw [ofReal_iteration_coefficient]
        have htE : (t : ℝ≥0∞) ≤ T := by exact_mod_cast ht
        exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl
          (add_le_add le_rfl htE)) le_rfl) le_rfl
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal
          (∫ s in (0 : ℝ)..t, C * A ^ n * s ^ (n + 1) / (n + 1).factorial) :=
        mul_le_mul' le_rfl henergy
      _ = _ := by
        rw [← ENNReal.ofReal_mul hA, integral_picard_envelope]


private theorem summable_sqrt_pow_div_factorial (a : ℝ) (ha : 0 ≤ a) :
    Summable (fun n : ℕ ↦ Real.sqrt (a ^ n / n.factorial)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (4 * a)
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hden : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have he : a ^ (n + 1) / (n + 1).factorial = (a / (n + 1)) * (a ^ n / n.factorial) := by
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    field_simp
  have hratio : a / (n + 1) ≤ (1 / 2 : ℝ) ^ 2 := by
    apply (div_le_iff₀ hn0).2
    have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _), he, Real.sqrt_mul (by positivity)]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (Real.sqrt_le_iff).2 ⟨by norm_num, hratio⟩


private theorem summable_sqrt_picard_envelope (C A t : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (ht : 0 ≤ t) :
    Summable (fun n : ℕ ↦ Real.sqrt (C * A ^ n * t ^ (n + 1) / (n + 1).factorial)) := by
  have hsum := (summable_sqrt_pow_div_factorial (A * t) (mul_nonneg hA ht)).mul_left
    (Real.sqrt (C * t))
  apply Summable.of_nonneg_of_le (fun n ↦ Real.sqrt_nonneg _) _ hsum
  intro n
  rw [← Real.sqrt_mul (mul_nonneg hC ht)]
  apply Real.sqrt_le_sqrt
  calc
    C * A ^ n * t ^ (n + 1) / (n + 1).factorial ≤
        C * A ^ n * t ^ (n + 1) / n.factorial := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast Nat.factorial_le (Nat.le_succ n)
    _ = C * t * ((A * t) ^ n / n.factorial) := by rw [mul_pow, pow_succ]; ring

private theorem eLpNorm_two_le_sqrt {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [NormedAddCommGroup E] {Z : Ω → E}
    (hZ : AEStronglyMeasurable Z P) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ ω, ‖Z ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal c) :
    eLpNorm Z 2 P ≤ ENNReal.ofReal (Real.sqrt c) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hZ]
  simp only [ENNReal.toReal_ofNat, one_div]
  apply (ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2)).2
  simpa only [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg c),
    Real.sq_sqrt hc] using h


private theorem exists_ae_L2_limit_of_summable_increments
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [CompleteSpace E]
    (Z : ℕ → Ω → E) (hZ : ∀ n, MemLp (Z n) 2 P)
    (hs : ∑' n, eLpNorm (Z (n + 1) - Z n) 2 P ≠ ∞) :
    ∃ W : Ω → E, MemLp W 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n ↦ Z n ω) atTop (𝓝 (W ω))) ∧
      Tendsto (fun n ↦ eLpNorm (Z n - W) 2 P) atTop (𝓝 0) := by
  let z (n : ℕ) : Lp E 2 P := (hZ n).toLp (Z n)
  have hnorm : ∑' n, ‖z (n + 1) - z n‖ₑ ≠ ∞ := by
    simpa only [z, ← MemLp.toLp_sub, Lp.eNorm_toLp] using hs
  have hc : CauchySeq z := by
    apply cauchySeq_of_summable_dist
    have he n : dist (z n) (z n.succ) = ‖z (n + 1) - z n‖ := by
      rw [dist_comm, dist_eq_norm]
    simpa only [he] using (tsum_eNorm_ne_top_iff_summable_norm.1 hnorm)
  obtain ⟨W, hW⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨W, Lp.memLp W, ?_, ?_⟩
  · have hsum := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2) hs
    obtain ⟨ns, hns, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hW).exists_seq_tendsto_ae
    have heq : ∀ᵐ ω ∂P, ∀ n, z n ω = Z n ω :=
      ae_all_iff.2 fun n ↦ (hZ n).coeFn_toLp
    filter_upwards [hsum, hsub, heq] with ω hω hsubω heqω
    have hcω : CauchySeq (fun n ↦ Z n ω) := by
      apply cauchySeq_of_summable_dist
      have he n : dist (Z n ω) (Z n.succ ω) = ‖Z (n + 1) ω - Z n ω‖ := by
        rw [dist_comm, dist_eq_norm]
      simpa only [he, Pi.sub_apply] using hω
    obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcω
    have he : v = W ω := tendsto_nhds_unique (hv.comp hns.tendsto_atTop)
      (by simpa only [heqω, Function.comp_def] using hsubω)
    exact he ▸ hv
  · have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' z W).1 hW
    apply h.congr
    intro n
    exact eLpNorm_congr_ae ((hZ n).coeFn_toLp.sub ae_eq_rfl)


private theorem exists_path_L2_limit_of_factorial_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    (X : ℕ → ℝ≥0 → Ω → ℝ)
    (hm : ∀ n t, Measurable (X n t)) (hc : ∀ n ω, Continuous (X n · ω))
    (x : ℝ) (h0 : X 0 = fun _ _ ↦ x) (T : ℝ≥0)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbound : ∀ n, ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) T,
      ‖X (n + 1) s ω - X n s ω‖ₑ) ^ 2 ∂P ≤
      ENNReal.ofReal (C * A ^ n * (T : ℝ) ^ (n + 1) / (n + 1).factorial)) :
    ∃ W : Ω → C(Icc (0 : ℝ≥0) T, ℝ), MemLp W 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n ↦
        (⟨fun s ↦ X n s ω, (hc n ω).comp continuous_subtype_val⟩ :
          C(Icc (0 : ℝ≥0) T, ℝ))) atTop (𝓝 (W ω))) ∧
      Tendsto (fun n ↦ eLpNorm (fun ω ↦
        (⟨fun s ↦ X n s ω, (hc n ω).comp continuous_subtype_val⟩ :
          C(Icc (0 : ℝ≥0) T, ℝ)) - W ω) 2 P) atTop (𝓝 0) := by
  let Z (n : ℕ) (ω : Ω) : C(Icc (0 : ℝ≥0) T, ℝ) :=
    ⟨fun s ↦ X n s ω, (hc n ω).comp continuous_subtype_val⟩
  have hZm n : Measurable (Z n) := ContinuousMap.measurable_iff_eval.2 (fun t ↦ hm n t)
  let c (n : ℕ) : ℝ := Real.sqrt (C * A ^ n * (T : ℝ) ^ (n + 1) / (n + 1).factorial)
  have hcs : Summable c := summable_sqrt_picard_envelope C A T hC hA T.coe_nonneg
  have hinc n : eLpNorm (Z (n + 1) - Z n) 2 P ≤ ENNReal.ofReal (c n) := by
    apply eLpNorm_two_le_sqrt ((hZm (n + 1)).sub (hZm n)).aestronglyMeasurable (by positivity)
    simpa only [Pi.sub_apply, ContinuousMap.eNorm_eq_iSup_eNorm, ContinuousMap.sub_apply,
      Z, ContinuousMap.coe_mk] using hbound n
  have hincLp n : MemLp (Z (n + 1) - Z n) 2 P :=
    (hinc n).trans_lt ENNReal.ofReal_lt_top
  have hZ : ∀ n, MemLp (Z n) 2 P := by
    intro n
    induction n with
    | zero =>
      have he : Z 0 = fun _ ↦ ContinuousMap.const (Icc (0 : ℝ≥0) T) x := by
        funext ω
        ext s
        exact congrFun (congrFun h0 s) ω
      rw [he]
      exact memLp_const _
    | succ n ih =>
      have he : Z (n + 1) = (Z (n + 1) - Z n) + Z n := by abel
      rw [he]
      exact (hincLp n).add ih
  have hs : ∑' n, eLpNorm (Z (n + 1) - Z n) 2 P ≠ ∞ :=
    ne_top_of_le_ne_top hcs.tsum_ofReal_ne_top (tsum_le_tsum hinc)
  exact exists_ae_L2_limit_of_summable_increments Z hZ hs


private theorem exists_continuous_adapted_limit
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P]
    (X : ℕ → ℝ≥0 → Ω → ℝ) (ha : ∀ n, Adapted F (X n))
    (hc : ∀ n ω, Continuous (X n · ω))
    (hlim : ∀ N : ℕ, ∃ W : Ω → C(Icc (0 : ℝ≥0) N, ℝ),
      ∀ᵐ ω ∂P, Tendsto (fun n ↦
        (⟨fun s ↦ X n s ω, (hc n ω).comp continuous_subtype_val⟩ :
          C(Icc (0 : ℝ≥0) N, ℝ))) atTop (𝓝 (W ω))) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Adapted F Y ∧ (∀ ω, Continuous (Y · ω)) ∧
      ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n ↦ X n t ω) atTop (𝓝 (Y t ω)) := by
  classical
  choose W hW using hlim
  let G : Set Ω := {ω | ∀ N : ℕ, Tendsto (fun n ↦
    (⟨fun s ↦ X n s ω, (hc n ω).comp continuous_subtype_val⟩ :
      C(Icc (0 : ℝ≥0) N, ℝ))) atTop (𝓝 (W N ω))}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := ae_all_iff.2 hW
  have hGm (t : ℝ≥0) : MeasurableSet[F t] G := by
    apply Filtration.IsComplete.measurableSet_of_ae_eq (μ := P) MeasurableSet.univ
    filter_upwards [hG] with ω hω
    simp only [mem_univ, iff_true]
    exact hω
  let Y (t : ℝ≥0) (ω : Ω) : ℝ := if ω ∈ G then limUnder atTop (fun n ↦ X n t ω) else 0
  have hpoint (ω : Ω) (hω : ω ∈ G) (N : ℕ) (t : Icc (0 : ℝ≥0) N) :
      Tendsto (fun n ↦ X n t ω) atTop (𝓝 (W N ω t)) :=
    ((continuous_eval_const t).tendsto (W N ω)).comp (hω N)
  have he (ω : Ω) (hω : ω ∈ G) (N : ℕ) (t : Icc (0 : ℝ≥0) N) :
      Y t ω = W N ω t := by
    simp only [Y, ite_eq_left hω]
    exact (hpoint ω hω N t).limUnder_eq
  have hYlim (ω : Ω) (hω : ω ∈ G) (t : ℝ≥0) :
      Tendsto (fun n ↦ X n t ω) atTop (𝓝 (Y t ω)) := by
    obtain ⟨N, hN⟩ := exists_nat_ge t
    rw [he ω hω N ⟨t, zero_le, hN⟩]
    exact hpoint ω hω N ⟨t, zero_le, hN⟩
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro t
    refine @measurable_of_tendsto_metrizable Ω ℝ (F t) _ _ _ _
      (fun n ω ↦ if ω ∈ G then X n t ω else 0) (Y t)
      (fun n ↦ Measurable.ite (hGm t) (ha n t) measurable_const) ?_
    apply tendsto_pi_nhds.2
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [ite_eq_left hω] using hYlim ω hω t
    · simpa only [Y, ite_eq_right hω] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  · intro ω
    by_cases hω : ω ∈ G
    · rw [continuous_iff_continuousAt]
      intro t
      obtain ⟨N, hN⟩ := exists_nat_gt t
      have hcon : ContinuousOn (Y · ω) (Icc (0 : ℝ≥0) N) := by
        apply continuousOn_iff_continuous_domRestrict.2
        have heq : (Icc (0 : ℝ≥0) N).domRestrict (Y · ω) = W N ω :=
          funext (he ω hω N)
        rw [heq]
        exact (W N ω).continuous
      apply hcon.continuousAt
      have hset : Icc (0 : ℝ≥0) N = Iic (N : ℝ≥0) := by ext s; simp
      rw [hset]
      exact Iic_mem_nhds hN
    · simpa only [Y, ite_eq_right hω] using (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ)))
  · filter_upwards [hG] with ω hω using hYlim ω hω


private theorem exists_scalar_sde_picard_path_limit
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    (x : ℝ) (X J : ℕ → ℝ≥0 → Ω → ℝ) (h0 : X 0 = fun _ _ ↦ x)
    (hX : ∀ n, IsProgressive F (X n) ∧ (∀ ω, Continuous (X n · ω)) ∧
      ∀ T, integrandDist P (X n) (fun _ _ ↦ 0) T ≠ ∞)
    (hJ : ∀ n, Martingale (J n) F P ∧ IsProgressive F (J n) ∧
      (∀ ω, Continuous (J n · ω)) ∧
      (∀ t, J n t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (X n s ω)) t) ∧
      X (n + 1) = fun t ω ↦ x + J n t ω + ∫ s in (0 : ℝ)..t, b (X n s.toNNReal ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, ∃ hYc : ∀ ω, Continuous (Y · ω), IsProgressive F Y ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ≥0, Tendsto (fun n ↦
        (⟨fun s ↦ X n s ω, ((hX n).2.1 ω).comp continuous_subtype_val⟩ :
          C(Icc (0 : ℝ≥0) T, ℝ))) atTop
        (𝓝 ⟨fun s ↦ Y s ω, (hYc ω).comp continuous_subtype_val⟩)) ∧
      ∀ T : ℝ≥0,
        MemLp (fun ω ↦ (⟨fun s ↦ Y s ω, (hYc ω).comp continuous_subtype_val⟩ :
          C(Icc (0 : ℝ≥0) T, ℝ))) 2 P ∧
        Tendsto (fun n ↦ eLpNorm (fun ω ↦
          (⟨fun s ↦ X n s ω, ((hX n).2.1 ω).comp continuous_subtype_val⟩ :
            C(Icc (0 : ℝ≥0) T, ℝ)) -
          ⟨fun s ↦ Y s ω, (hYc ω).comp continuous_subtype_val⟩) 2 P) atTop (𝓝 0) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  let Z (T : ℝ≥0) (n : ℕ) (ω : Ω) : C(Icc (0 : ℝ≥0) T, ℝ) :=
    ⟨fun s ↦ X n s ω, ((hX n).2.1 ω).comp continuous_subtype_val⟩
  have hcap (T : ℝ≥0) : ∃ W : Ω → C(Icc (0 : ℝ≥0) T, ℝ), MemLp W 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n ↦ Z T n ω) atTop (𝓝 (W ω))) ∧
      Tendsto (fun n ↦ eLpNorm (Z T n - W) 2 P) atTop (𝓝 0) := by
    apply exists_path_L2_limit_of_factorial_bound X
      (fun n t ↦ (hX n).1.adapted.measurable) (fun n ↦ (hX n).2.1) x h0 T
      (8 * (σ x) ^ 2 + 2 * (T : ℝ) * (b x) ^ 2)
      (2 * (4 + (T : ℝ)) * (K : ℝ) ^ 2) (by positivity) (by positivity)
    exact fun n ↦ lintegral_iSup_picard_succ_sub_sq_le hB hBF hInd hσ hb x X J h0 hX hJ T n T le_rfl
  obtain ⟨Y, hYa, hYc, hpoint⟩ := exists_continuous_adapted_limit X
    (fun n ↦ (hX n).1.adapted) (fun n ↦ (hX n).2.1) (fun N ↦ by
      obtain ⟨W, -, hw, -⟩ := hcap N
      exact ⟨W, hw⟩)
  let V (T : ℝ≥0) (ω : Ω) : C(Icc (0 : ℝ≥0) T, ℝ) :=
    ⟨fun s ↦ Y s ω, (hYc ω).comp continuous_subtype_val⟩
  have hV (T : ℝ≥0) : MemLp (V T) 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n ↦ Z T n ω) atTop (𝓝 (V T ω))) ∧
      Tendsto (fun n ↦ eLpNorm (Z T n - V T) 2 P) atTop (𝓝 0) := by
    obtain ⟨W, hwLp, hw, hwL2⟩ := hcap T
    have he : W =ᵐ[P] V T := by
      filter_upwards [hpoint, hw] with ω hω hwω
      ext t
      exact tendsto_nhds_unique
        (((continuous_eval_const t).tendsto (W ω)).comp hwω) (hω t)
    refine ⟨(memLp_congr_ae he).1 hwLp, ?_, ?_⟩
    · filter_upwards [hw, he] with ω hω heω using heω ▸ hω
    · apply hwL2.congr
      intro n
      exact eLpNorm_congr_ae (ae_eq_rfl.sub he)
  refine ⟨Y, hYc, (hYa.stronglyAdapted.isStronglyProgressive_of_continuous hYc).isProgressive,
    ?_, fun T ↦ ⟨(hV T).1, (hV T).2.2⟩⟩
  have hnat : ∀ᵐ ω ∂P, ∀ N : ℕ, Tendsto (fun n ↦ Z N n ω) atTop (𝓝 (V N ω)) :=
    ae_all_iff.2 (fun N ↦ (hV N).2.1)
  filter_upwards [hnat] with ω hω
  intro T
  obtain ⟨N, hN⟩ := exists_nat_ge T
  let inc : C(Icc (0 : ℝ≥0) T, Icc (0 : ℝ≥0) N) :=
    ⟨fun s ↦ ⟨s, s.property.1, s.property.2.trans hN⟩,
      continuous_subtype_val.subtype_mk _⟩
  exact ((ContinuousMap.continuous_precomp inc).tendsto (V N ω)).comp (hω N)

/-- Actual scalar Lipschitz Picard iterates converge to one progressive process
with every-path continuity. Outside a single null set the convergence is uniform
on every finite interval. Each limiting running maximum has finite second moment,
and the corresponding mean-square supremum error tends to zero.

Filtration completeness permits a common null-set fallback while preserving
adaptedness. This theorem proves convergence, without asserting the limiting
integral equation. -/
theorem exists_scalar_sde_picard_limit
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    (x : ℝ) (X J : ℕ → ℝ≥0 → Ω → ℝ) (h0 : X 0 = fun _ _ ↦ x)
    (hX : ∀ n, IsProgressive F (X n) ∧ (∀ ω, Continuous (X n · ω)) ∧
      ∀ T, integrandDist P (X n) (fun _ _ ↦ 0) T ≠ ∞)
    (hJ : ∀ n, Martingale (J n) F P ∧ IsProgressive F (J n) ∧
      (∀ ω, Continuous (J n · ω)) ∧
      (∀ t, J n t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (X n s ω)) t) ∧
      X (n + 1) = fun t ω ↦ x + J n t ω + ∫ s in (0 : ℝ)..t, b (X n s.toNNReal ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, IsProgressive F Y ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun n s ↦ X n s ω) (Y · ω) atTop (Icc 0 T)) ∧
      ∀ T : ℝ≥0,
        (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) T, ‖Y s ω‖ₑ) ^ 2 ∂P) ≠ ∞ ∧
        Tendsto (fun n ↦ ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) T,
          ‖X n s ω - Y s ω‖ₑ) ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨Y, hYc, hYp, hU, hL⟩ := exists_scalar_sde_picard_path_limit
    hB hBF hInd hσ hb x X J h0 hX hJ
  refine ⟨Y, hYp, hYc, ?_, ?_⟩
  · filter_upwards [hU] with ω hω
    intro T
    exact ((hYc ω).continuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn
      (fun n ↦ ((hX n).2.1 ω).continuousOn)).1 (hω T)
  · intro T
    let Z (n : ℕ) (ω : Ω) : C(Icc (0 : ℝ≥0) T, ℝ) :=
      ⟨fun s ↦ X n s ω, ((hX n).2.1 ω).comp continuous_subtype_val⟩
    let V (ω : Ω) : C(Icc (0 : ℝ≥0) T, ℝ) :=
      ⟨fun s ↦ Y s ω, (hYc ω).comp continuous_subtype_val⟩
    have hZm n : Measurable (Z n) := ContinuousMap.measurable_iff_eval.2
      (fun s ↦ (hX n).1.adapted.measurable)
    have hVm : Measurable V := ContinuousMap.measurable_iff_eval.2
      (fun s ↦ hYp.adapted.measurable)
    have he n : ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) T, ‖X n s ω - Y s ω‖ₑ) ^ 2 ∂P =
        (eLpNorm (Z n - V) 2 P) ^ 2 := by
      have h := eLpNorm_nnreal_pow_eq_lintegral (μ := P) (p := (2 : ℝ≥0)) (by norm_num)
        ((hZm n).sub hVm).aestronglyMeasurable
      simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
        Pi.sub_apply, ContinuousMap.eNorm_eq_iSup_eNorm, ContinuousMap.sub_apply,
        Z, V, ContinuousMap.coe_mk] using h.symm
    constructor
    · have h := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hL T).1
      simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two,
        ContinuousMap.eNorm_eq_iSup_eNorm, ContinuousMap.coe_mk] using h.ne
    · simp only [he]
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), Z, V, Pi.sub_def] using
        (ENNReal.Tendsto.pow (n := 2) (hL T).2)

end ProbabilityTheory
