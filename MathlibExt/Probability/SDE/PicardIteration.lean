/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.SDE.ItoVersionEnergy
public import MathlibExt.Probability.SDE.LipschitzIntegrands
public import MathlibExt.Probability.SDE.TimeIntegrals
import MathlibExt.Probability.ContinuousDoob
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.Finiteness

/-!
# Scalar SDE Picard iteration and maximal estimates

Construct the actual Picard sequence on all nonnegative times. Each stochastic
update uses an adapted continuous martingale version, and each drift update is
the ordinary time integral. Doob and Cauchy–Schwarz give the maximal difference
and initial-increment estimates for the classical factorial convergence argument.
This module constructs the iterates and estimates them; it does not assert their
convergence for general coefficients.

The construction uses the complete-filtration convention of Le Gall, *Brownian
Motion, Martingales, and Stochastic Calculus* (2016), Definition 8.1 and Theorem
8.3. Completeness is sufficient for this construction and is not claimed
necessary. The estimates themselves retain arbitrary filtrations and pre-Brownian
laws. No pathwise linearity of the continuous-version selector is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

private theorem energy_add {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsProgressive F X) (hY : IsProgressive F Y) (T : ℝ≥0)
    (hx : integrandDist P X (fun _ _ ↦ 0) T ≠ ∞)
    (hy : integrandDist P Y (fun _ _ ↦ 0) T ≠ ∞) :
    integrandDist P (fun t ω ↦ X t ω + Y t ω) (fun _ _ ↦ 0) T ≠ ∞ := by
  have hmX := IsProgressive.measurable_toNNReal hX
  have hmY := IsProgressive.measurable_toNNReal hY
  have h := integrandDist_le (P := P) (X := fun t ω ↦ X t ω + Y t ω) (Y := fun _ _ ↦ 0)
    (Z := X) (hmX.add hmY) measurable_const hmX T
  have hb : integrandDist P (fun t ω ↦ X t ω + Y t ω) (fun _ _ ↦ 0) T ≤
      2 * integrandDist P Y (fun _ _ ↦ 0) T + 2 * integrandDist P X (fun _ _ ↦ 0) T := by
    simpa only [integrandDist, add_sub_cancel_left, sub_zero, zero_sub, eNorm_neg] using h
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by norm_num) hy, ENNReal.mul_ne_top (by norm_num) hx⟩) hb

private theorem energy_const {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (x : ℝ) (T : ℝ≥0) :
    integrandDist P (fun _ _ ↦ x) (fun _ _ ↦ 0) T ≠ ∞ := by
  simp only [integrandDist, sub_zero, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc]
  finiteness

private theorem exists_picard_step {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B X : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    (hXp : IsProgressive F X) (hXc : ∀ ω, Continuous (X · ω))
    (hXe : ∀ T, integrandDist P X (fun _ _ ↦ 0) T ≠ ∞) (x : ℝ) :
    ∃ J : ℝ≥0 → Ω → ℝ, Martingale J F P ∧ IsProgressive F J ∧
      (∀ ω, Continuous (J · ω)) ∧
      (∀ t, J t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (X s ω)) t) ∧
      IsProgressive F (fun t ω ↦ x + J t ω + ∫ s in (0 : ℝ)..t, b (X s.toNNReal ω)) ∧
      (∀ ω, Continuous fun t : ℝ≥0 ↦ x + J t ω + ∫ s in (0 : ℝ)..t, b (X s.toNNReal ω)) ∧
      ∀ T, integrandDist P
        (fun t ω ↦ x + J t ω + ∫ s in (0 : ℝ)..t, b (X s.toNNReal ω))
        (fun _ _ ↦ 0) T ≠ ∞ := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hsp : IsProgressive F (fun s ω ↦ σ (X s ω)) :=
    fun T ↦ hσ.continuous.measurable.comp (hXp T)
  have hbp : IsProgressive F (fun s ω ↦ b (X s ω)) :=
    fun T ↦ hb.continuous.measurable.comp (hXp T)
  have hbc : ∀ ω, Continuous (fun s ↦ b (X s ω)) :=
    fun ω ↦ hb.continuous.comp (hXc ω)
  obtain ⟨J, hJm, hJp, hJc, hJeq, hJe, -⟩ :=
    itoIntegral_exists_continuous_martingale_finite_energy hB hBF hInd hsp
      (fun T ↦ integrandDist_comp_zero_ne_top hXp hσ T (hXe T))
  have hdp := IsProgressive.timeIntegral hbp hbc
  have hde (T : ℝ≥0) : integrandDist P
      (fun t ω ↦ ∫ s in (0 : ℝ)..t, b (X s.toNNReal ω)) (fun _ _ ↦ 0) T ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by finiteness)
        (integrandDist_comp_zero_ne_top hXp hb T (hXe T)))
      (integrandDist_timeIntegral_zero_le P hbc T)
  have hxp : IsProgressive F (fun _ _ ↦ x) := isProgressive_const F x
  have hsum : IsProgressive F (fun t ω ↦ x + J t ω) := fun T ↦ (hxp T).add (hJp T)
  refine ⟨J, hJm, hJp, hJc, hJeq, fun T ↦ (hsum T).add (hdp T), ?_, ?_⟩
  · intro ω
    exact (continuous_const.add (hJc ω)).add (continuous_timeIntegral (hbc ω))
  · intro T
    exact energy_add hsum hdp T (energy_add hxp hJp T (energy_const P x T) (hJe T)) (hde T)

/-- Construct actual all-time scalar Picard iterates from deterministic initial data.
Every iterate is progressive, continuous on every path and locally finite-energy.
Each update uses a continuous martingale version of the actual Itô integral plus
the ordinary drift integral. The original filtration is explicitly complete;
no convergence or SDE solution is assumed or concluded by this construction. -/
theorem exists_scalar_sde_picard_sequence {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    (x : ℝ) :
    ∃ X J : ℕ → ℝ≥0 → Ω → ℝ, X 0 = (fun _ _ ↦ x) ∧
      (∀ n, IsProgressive F (X n) ∧ (∀ ω, Continuous (X n · ω)) ∧
        ∀ T, integrandDist P (X n) (fun _ _ ↦ 0) T ≠ ∞) ∧
      ∀ n, Martingale (J n) F P ∧ IsProgressive F (J n) ∧
        (∀ ω, Continuous (J n · ω)) ∧
        (∀ t, J n t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (X n s ω)) t) ∧
        X (n + 1) = (fun t ω ↦ x + J n t ω + ∫ s in (0 : ℝ)..t, b (X n s.toNNReal ω)) := by
  classical
  have := hB.isGaussianProcess.isProbabilityMeasure
  let S := {Y : ℝ≥0 → Ω → ℝ // IsProgressive F Y ∧
    (∀ ω, Continuous (Y · ω)) ∧ ∀ T, integrandDist P Y (fun _ _ ↦ 0) T ≠ ∞}
  have H (Y : S) := exists_picard_step hB hBF hInd hσ hb Y.2.1 Y.2.2.1 Y.2.2.2 x
  let Jstep (Y : S) : ℝ≥0 → Ω → ℝ := Classical.choose (H Y)
  have hJstep (Y : S) := Classical.choose_spec (H Y)
  let step (Y : S) : S := ⟨fun t ω ↦ x + Jstep Y t ω +
      ∫ s in (0 : ℝ)..t, b (Y.1 s.toNNReal ω), (hJstep Y).2.2.2.2⟩
  let initial : S := ⟨fun _ _ ↦ x, isProgressive_const F x,
    fun _ ↦ continuous_const, energy_const P x⟩
  let seq : ℕ → S := Nat.rec initial (fun _ Y ↦ step Y)
  refine ⟨fun n ↦ (seq n).1, fun n ↦ Jstep (seq n), rfl, fun n ↦ (seq n).2, ?_⟩
  intro n
  exact ⟨(hJstep (seq n)).1, (hJstep (seq n)).2.1,
    (hJstep (seq n)).2.2.1, (hJstep (seq n)).2.2.2.1, rfl⟩

/-- Doob's inequality and the actual difference isometry bound the squared running
maximum of two continuous martingale Itô versions after a Lipschitz composition.
Version selection need not be pathwise linear. No filtration completeness is
needed; only the input energies on the specified horizon must be finite. -/
theorem lintegral_iSup_ito_version_sub_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B X Y J L : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ)
    (hXp : IsProgressive F X) (hYp : IsProgressive F Y)
    (hJm : Martingale J F P) (hLm : Martingale L F P)
    (hJc : ∀ ω, Continuous (J · ω)) (hLc : ∀ ω, Continuous (L · ω))
    (hJe : ∀ t, J t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (X s ω)) t)
    (hLe : ∀ t, L t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (Y s ω)) t)
    (t : ℝ≥0) (hXe : integrandDist P X (fun _ _ ↦ 0) t ≠ ∞)
    (hYe : integrandDist P Y (fun _ _ ↦ 0) t ≠ ∞) :
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖J s ω - L s ω‖ₑ)^2 ∂P ≤
      4 * (K : ℝ≥0∞)^2 * integrandDist P X Y t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hJ2 (s : ℝ≥0) : MemLp (J s) 2 P :=
    (memLp_itoIntegral P F B (fun u ω ↦ σ (X u ω)) s).ae_eq (hJe s).symm
  have hL2 (s : ℝ≥0) : MemLp (L s) 2 P :=
    (memLp_itoIntegral P F B (fun u ω ↦ σ (Y u ω)) s).ae_eq (hLe s).symm
  have hd := (hJm.sub hLm).lintegral_iSup_sq_le_of_continuous
    (fun ω ↦ (hJc ω).sub (hLc ω)) (fun s ↦ (hJ2 s).sub (hL2 s)) t
  calc
    _ ≤ 4 * ∫⁻ ω, ‖J t ω - L t ω‖ₑ^2 ∂P := by
      simpa only [Pi.sub_apply, Real.eNorm_eq_ofReal_abs,
        ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] using hd
    _ = 4 * ∫⁻ ω, ‖itoIntegral P F B (fun s ω ↦ σ (X s ω)) t ω -
        itoIntegral P F B (fun s ω ↦ σ (Y s ω)) t ω‖ₑ^2 ∂P := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [hJe t, hLe t] with ω hJ hL
      rw [hJ, hL]
    _ ≤ 4 * ((K : ℝ≥0∞)^2 * integrandDist P X Y t) :=
      mul_le_mul' le_rfl
        (lintegral_itoIntegral_sub_comp_lipschitz_le hB hBF hInd hXp hYp hσ t hXe hYe)
    _ = _ := by ring

private theorem measurable_path_sup {Ω : Type*} [MeasurableSpace Ω]
    {H : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (H t))
    (hc : ∀ ω, Continuous (H · ω)) (T : ℝ≥0) :
    Measurable fun ω ↦ ⨆ s : Icc (0 : ℝ≥0) T, ‖H s ω‖ₑ := by
  let Z : Ω → C(Icc (0 : ℝ≥0) T, ℝ) :=
    fun ω ↦ ⟨fun s ↦ H s ω, (hc ω).comp continuous_subtype_val⟩
  have hz : Measurable Z := ContinuousMap.measurable_iff_eval.2 (fun s ↦ hm s)
  simpa only [ContinuousMap.eNorm_eq_iSup_eNorm, Z, ContinuousMap.coe_mk] using hz.eNorm

/-- The squared running maximum of the difference of actual ordinary integrals
after a Lipschitz composition is bounded by elapsed time times `K²` times the
input energy distance. Continuous paths ensure ordinary integrability; no sample
measurability or finite-measure assumption is required for this lower-integral bound. -/
theorem lintegral_iSup_timeIntegral_comp_sub_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X Y : ℝ≥0 → Ω → ℝ} {b : ℝ → ℝ} {K : ℝ≥0} (hb : LipschitzWith K b)
    (hXc : ∀ ω, Continuous (X · ω)) (hYc : ∀ ω, Continuous (Y · ω)) (t : ℝ≥0) :
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t,
      ‖(∫ u in (0 : ℝ)..s, b (X u.toNNReal ω)) -
        (∫ u in (0 : ℝ)..s, b (Y u.toNNReal ω))‖ₑ)^2 ∂P ≤
      (t : ℝ≥0∞) * (K : ℝ≥0∞)^2 * integrandDist P X Y t := by
  let : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, zero_le⟩⟩
  have hc (ω) : Continuous (fun s ↦ b (X s ω) - b (Y s ω)) :=
    (hb.continuous.comp (hXc ω)).sub (hb.continuous.comp (hYc ω))
  have he (ω) (s : ℝ≥0) :
      (∫ u in (0 : ℝ)..s, b (X u.toNNReal ω)) -
        (∫ u in (0 : ℝ)..s, b (Y u.toNNReal ω)) =
      ∫ u in (0 : ℝ)..s, b (X u.toNNReal ω) - b (Y u.toNNReal ω) := by
    symm
    exact intervalIntegral.integral_sub
      ((hb.continuous.comp (hXc ω) |>.comp continuous_real_toNNReal).intervalIntegrable _ _)
      ((hb.continuous.comp (hYc ω) |>.comp continuous_real_toNNReal).intervalIntegrable _ _)
  calc
    _ ≤ ∫⁻ ω, ⨆ (s : ℝ≥0) (_ : s ≤ t),
        ‖∫ u in (0 : ℝ)..s, b (X u.toNNReal ω) - b (Y u.toNNReal ω)‖ₑ^2 ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [ENNReal.iSup_pow]
      refine iSup_le fun s ↦ ?_
      rw [he]
      exact le_iSup_of_le s (le_iSup_of_le s.2.2 le_rfl)
    _ ≤ (t : ℝ≥0∞) * integrandDist P (fun s ω ↦ b (X s ω) - b (Y s ω))
        (fun _ _ ↦ 0) t := lintegral_iSup_timeIntegral_sq_le P hc t
    _ ≤ (t : ℝ≥0∞) * ((K : ℝ≥0∞)^2 * integrandDist P X Y t) := by
      apply mul_le_mul' le_rfl
      simpa only [integrandDist, sub_zero] using integrandDist_comp_lipschitz_le hb P X Y t
    _ = _ := by ring

private theorem enorm_add_sq_le (a b : ℝ) :
    ‖a + b‖ₑ^2 ≤ 2 * ‖a‖ₑ^2 + 2 * ‖b‖ₑ^2 := by
  have he := ENNReal.ofReal_le_ofReal (show (a + b)^2 ≤ 2 * a^2 + 2 * b^2 by
    nlinarith [sq_nonneg (a - b)])
  simpa only [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
    ENNReal.ofReal_add (by positivity : 0 ≤ 2 * a^2) (by positivity : 0 ≤ 2 * b^2),
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), ENNReal.ofReal_ofNat] using he

private theorem lintegral_sup_add_sq_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {U V : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (U t))
    (hc : ∀ ω, Continuous (U · ω)) (t : ℝ≥0) :
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖U s ω + V s ω‖ₑ)^2 ∂P ≤
      2 * (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖U s ω‖ₑ)^2 ∂P) +
      2 * (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖V s ω‖ₑ)^2 ∂P) := by
  let : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, zero_le⟩⟩
  have hms := (measurable_path_sup hm hc t).pow_const 2
  calc
    _ ≤ ∫⁻ ω, 2 * (⨆ s : Icc (0 : ℝ≥0) t, ‖U s ω‖ₑ)^2 +
        2 * (⨆ s : Icc (0 : ℝ≥0) t, ‖V s ω‖ₑ)^2 ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [ENNReal.iSup_pow]
      refine iSup_le fun s ↦ (enorm_add_sq_le _ _).trans ?_
      exact add_le_add
        (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le
          (le_iSup (fun r : Icc (0 : ℝ≥0) t ↦ ‖U r ω‖ₑ) s) 2))
        (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le
          (le_iSup (fun r : Icc (0 : ℝ≥0) t ↦ ‖V r ω‖ₑ) s) 2))
    _ = _ := by
      rw [lintegral_add_left' (show AEMeasurable
        (fun ω ↦ 2 * (⨆ s : Icc (0 : ℝ≥0) t, ‖U s ω‖ₑ)^2) P from
          (measurable_const.mul hms).aemeasurable),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]

/-- Two actual Picard updates with the same deterministic starting value satisfy
the maximal difference bound `2*(4+t)*K²` times the integrated input distance.
The stochastic versions are continuous martingales with fixed-time actual Itô
equality. No completeness, right continuity or continuous integrator paths are
assumed for this estimate. The input processes have continuous paths. -/
theorem lintegral_iSup_picard_sub_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B X Y J L : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
    (hXp : IsProgressive F X) (hYp : IsProgressive F Y)
    (hXc : ∀ ω, Continuous (X · ω)) (hYc : ∀ ω, Continuous (Y · ω))
    (hJm : Martingale J F P) (hLm : Martingale L F P)
    (hJc : ∀ ω, Continuous (J · ω)) (hLc : ∀ ω, Continuous (L · ω))
    (hJe : ∀ t, J t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (X s ω)) t)
    (hLe : ∀ t, L t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (Y s ω)) t)
    (x : ℝ) (t : ℝ≥0) (hXe : integrandDist P X (fun _ _ ↦ 0) t ≠ ∞)
    (hYe : integrandDist P Y (fun _ _ ↦ 0) t ≠ ∞) :
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t,
      ‖(x + J s ω + ∫ u in (0 : ℝ)..s, b (X u.toNNReal ω)) -
        (x + L s ω + ∫ u in (0 : ℝ)..s, b (Y u.toNNReal ω))‖ₑ)^2 ∂P ≤
      2 * (4 + (t : ℝ≥0∞)) * (K : ℝ≥0∞)^2 * integrandDist P X Y t := by
  have hA := lintegral_iSup_ito_version_sub_le hB hBF hInd hσ hXp hYp
    hJm hLm hJc hLc hJe hLe t hXe hYe
  have hD := lintegral_iSup_timeIntegral_comp_sub_le P hb hXc hYc t
  have he (s : Icc (0 : ℝ≥0) t) (ω : Ω) :
      (x + J s ω + ∫ u in (0 : ℝ)..s, b (X u.toNNReal ω)) -
        (x + L s ω + ∫ u in (0 : ℝ)..s, b (Y u.toNNReal ω)) =
      (J s ω - L s ω) + ((∫ u in (0 : ℝ)..s, b (X u.toNNReal ω)) -
        ∫ u in (0 : ℝ)..s, b (Y u.toNNReal ω)) := by ring
  simp_rw [he]
  refine (lintegral_sup_add_sq_le P
    (U := fun s ω ↦ J s ω - L s ω)
    (V := fun s ω ↦ (∫ u in (0 : ℝ)..s, b (X u.toNNReal ω)) -
      ∫ u in (0 : ℝ)..s, b (Y u.toNNReal ω))
    (fun s ↦ ((hJm.1 s).mono (F.le s)).measurable.sub
      ((hLm.1 s).mono (F.le s)).measurable)
    (fun ω ↦ (hJc ω).sub (hLc ω)) t).trans ?_
  calc
    _ ≤ 2 * (4 * (K : ℝ≥0∞)^2 * integrandDist P X Y t) +
        2 * ((t : ℝ≥0∞) * (K : ℝ≥0∞)^2 * integrandDist P X Y t) :=
      add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hD)
    _ = _ := by ring

/-- A continuous martingale version of the actual Itô integral has squared running
maximum bounded by four times the integrand energy. This is Doob's inequality
combined with the isometry. Finite energy is needed only on the chosen horizon;
neither filtration completeness nor continuous integrator paths are assumed. -/
theorem lintegral_iSup_ito_version_sq_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B H J : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (hH : IsProgressive F H) (hJm : Martingale J F P)
    (hJc : ∀ ω, Continuous (J · ω))
    (hJe : ∀ t, J t =ᵐ[P] itoIntegral P F B H t)
    (t : ℝ≥0) (hHe : integrandDist P H (fun _ _ ↦ 0) t ≠ ∞) :
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖J s ω‖ₑ)^2 ∂P ≤
      4 * integrandDist P H (fun _ _ ↦ 0) t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hJ2 (s : ℝ≥0) : MemLp (J s) 2 P :=
    (memLp_itoIntegral P F B H s).ae_eq (hJe s).symm
  have hd := hJm.lintegral_iSup_sq_le_of_continuous hJc hJ2 t
  calc
    _ ≤ 4 * ∫⁻ ω, ‖J t ω‖ₑ^2 ∂P := by
      simpa only [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] using hd
    _ = 4 * ∫⁻ ω, ‖itoIntegral P F B H t ω‖ₑ^2 ∂P := by
      congr 1
      exact lintegral_congr_ae ((hJe t).fun_comp (fun z ↦ ‖z‖ₑ^2))
    _ = _ := by
      congr 1
      simpa only [integrandDist, sub_zero] using
        lintegral_itoIntegral_sq_of_isProgressive hB hBF hInd hH t
          (by simpa only [integrandDist, sub_zero] using hHe)

/-- The initial Picard increment for constant diffusion `a` and drift `c` has
squared running maximum at most `(8*|a|²+2*t*|c|²)*t`. The noise term is any
continuous martingale version of the actual constant-integrand Itô integral.
The estimate permits zero time and zero coefficients; its constants are nonoptimal. -/
theorem lintegral_iSup_ito_const_add_drift_sq_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B J : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (a c : ℝ) (hJm : Martingale J F P) (hJc : ∀ ω, Continuous (J · ω))
    (hJe : ∀ t, J t =ᵐ[P] itoIntegral P F B (fun _ _ ↦ a) t) (t : ℝ≥0) :
    ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖J s ω + (s : ℝ) * c‖ₑ)^2 ∂P ≤
      (8 * ‖a‖ₑ^2 + 2 * (t : ℝ≥0∞) * ‖c‖ₑ^2) * (t : ℝ≥0∞) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hA := lintegral_iSup_ito_version_sq_le hB hBF hInd (isProgressive_const F a)
    hJm hJc hJe t (energy_const P a t)
  have hAe : integrandDist P (fun _ _ ↦ a) (fun _ _ ↦ 0) t = ‖a‖ₑ^2 * (t : ℝ≥0∞) := by
    simp [integrandDist, Real.volume_Ioc]
  rw [hAe] at hA
  have hD := lintegral_iSup_timeIntegral_comp_sub_le P (X := fun _ _ ↦ c) (Y := fun _ _ ↦ 0)
    LipschitzWith.id (fun _ ↦ continuous_const) (fun _ ↦ continuous_const) t
  have hDe : integrandDist P (fun _ _ ↦ c) (fun _ _ ↦ 0) t = ‖c‖ₑ^2 * (t : ℝ≥0∞) := by
    simp [integrandDist, Real.volume_Ioc]
  rw [hDe] at hD
  simp only [id_eq, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    ENNReal.coe_one, one_pow, mul_one, mul_zero] at hD
  calc
    _ ≤ 2 * (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖J s ω‖ₑ)^2 ∂P) +
        2 * (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖(s : ℝ) * c‖ₑ)^2 ∂P) :=
      lintegral_sup_add_sq_le P (U := J) (V := fun s _ ↦ (s : ℝ) * c)
        (fun s ↦ ((hJm.1 s).mono (F.le s)).measurable) hJc t
    _ ≤ 2 * (4 * (‖a‖ₑ^2 * (t : ℝ≥0∞))) +
        2 * ((t : ℝ≥0∞) * (‖c‖ₑ^2 * (t : ℝ≥0∞))) :=
      add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hD)
    _ = _ := by ring

end ProbabilityTheory
