/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CompensatorUniquenessCadlag
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

namespace MathlibExtTest.Probability.Statistics.CompensatorUniquenessCadlag

/-! ### Explicit inputs -/

/-- With `T = 2`, `C = 3` (exit at `X = 2`), the observed process at `u = 7` equals its value at
`s = 4`, computed from the definitions. -/
example (ω : ℝ) :
    observedProcess (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) 7 ω = (1, 0) ∧
      observedProcess (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) 4 ω = (1, 0) := by
  norm_num [observedProcess, countingProcess, censoringProcess]

/-- The same, from `observedProcess_of_obsTime_le`. -/
example (ω : ℝ) :
    observedProcess (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) 7 ω =
      observedProcess (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) 4 ω :=
  observedProcess_of_obsTime_le (by norm_num [obsTime]) (by norm_num)

/-- The counting process with `T = 2`, `C = 3` jumps at `2`: it is `0` just before and `1` at the
jump, so it is right-continuous there but not left-continuous. -/
example (ω : ℝ) : countingProcess (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) 2 ω = 1 ∧
    ∀ t < 2, countingProcess (fun _ : ℝ => (2 : ℝ)) (fun _ => 3) t ω = 0 := by
  refine ⟨by norm_num [countingProcess], fun t ht => ?_⟩
  simp [countingProcess, not_le.2 ht]

/-! ### The Gaussian model: standard Gaussian failure time, censoring at `1` -/

/-- The standard Gaussian law charges every right half-line. -/
theorem gaussianReal_Ici_ne_zero (s : ℝ) : gaussianReal 0 1 (Ici s) ≠ 0 := fun h => by
  have := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
  simp [Real.volume_Ici] at this

/-- Hence its hazard measure is finite on every left half-line. -/
theorem hazard_gaussian_Iic_ne_top (s : ℝ) :
    hazardMeasure ((gaussianReal 0 1).map id) (Iic s) ≠ ∞ := by
  rw [Measure.map_id]
  exact hazardMeasure_Iic_ne_top (gaussianReal_Ici_ne_zero s)

/-- The exit time of the Gaussian model. -/
local notation "Xg" => obsTime (id : ℝ → ℝ) (fun _ : ℝ => (1 : ℝ))

/-- The model compensator `A(t) = Λ((-∞, t ∧ X])` of the Gaussian model. -/
local notation "Ag" =>
  compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure (Measure.map id (gaussianReal 0 1)))

/-- The history filtration of the Gaussian model. -/
local notation "ℱg" =>
  historyFiltration (T := id) (C := fun _ : ℝ => (1 : ℝ)) measurable_id measurable_const

theorem fv_Ag (ω : ℝ) : LocallyBoundedVariationOn (fun t => Ag t ω) univ :=
  ((monotone_compensator (hazard_gaussian_Iic_ne_top _)).monotoneOn univ).locallyBoundedVariationOn

theorem lim_Ag (ω : ℝ) : Tendsto (fun t => Ag t ω) atBot (𝓝 0) :=
  tendsto_compensator_atBot (hazard_gaussian_Iic_ne_top _)

/-- Every path of the Gaussian model compensator is right-continuous: `a ↦ Λ((-∞, a])` is
right-continuous by continuity from above (`Λ` is finite on left half-lines), and `t ↦ t ∧ X` is
continuous and monotone. -/
theorem continuousWithinAt_Ag (ω t : ℝ) : ContinuousWithinAt (fun s => Ag s ω) (Ici t) t := by
  set Λ := hazardMeasure (Measure.map id (gaussianReal 0 1)) with hΛ
  have hR : ∀ a : ℝ, ContinuousWithinAt (fun s => (Λ (Iic s)).toReal) (Ici a) a := by
    intro a
    have h := tendsto_measure_biInter_gt (μ := Λ) (s := fun r : ℝ => Iic r) (a := a)
      (fun r _ => measurableSet_Iic.nullMeasurableSet) (fun i j _ hij => Iic_subset_Iic.2 hij)
      ⟨a + 1, by linarith, hazard_gaussian_Iic_ne_top _⟩
    have hI : (⋂ r > a, Iic r) = Iic a := by
      ext x
      simp only [mem_iInter, mem_Iic]
      exact ⟨fun h => le_of_forall_gt_imp_ge_of_dense h, fun h r hr => h.trans hr.le⟩
    rw [hI] at h
    rw [← continuousWithinAt_Ioi_iff_Ici]
    exact (ENNReal.tendsto_toReal (hazard_gaussian_Iic_ne_top a)).comp h
  have hcont : ContinuousWithinAt (fun s => min s (Xg ω)) (Ici t) t :=
    (continuous_id.min continuous_const).continuousWithinAt
  have hmaps : MapsTo (fun s => min s (Xg ω)) (Ici t) (Ici (min t (Xg ω))) :=
    fun s (hs : t ≤ s) => min_le_min_right _ hs
  have hfun : (fun s => Ag s ω) = (fun s => (Λ (Iic s)).toReal) ∘ fun s => min s (Xg ω) :=
    funext fun s => compensator_eq _ _ _
  rw [hfun]
  exact ContinuousWithinAt.comp (f := fun s => min s (Xg ω)) (x := t) (hR _) hcont hmaps

theorem hind_g : IndepFun id (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) :=
  indepFun_const_right _ _

/-- **Non-vacuity** of the abstract càdlàg theorem: every hypothesis of
`ae_forall_eq_of_isCompensator_cadlag_history` (including right-continuity and the derived
"nothing learned after exit") holds for the Gaussian model compensator. -/
example : ∀ᵐ ω ∂(gaussianReal 0 1), ∀ t, Ag t ω = Ag t ω :=
  ae_forall_eq_of_isCompensator_cadlag_history measurable_id measurable_const
    (martingale_compensatedProcess measurable_id measurable_const hind_g)
    (martingale_compensatedProcess measurable_id measurable_const hind_g)
    (measurable_compensator_strictPast measurable_id measurable_const _)
    (measurable_compensator_strictPast measurable_id measurable_const _)
    continuousWithinAt_Ag continuousWithinAt_Ag (ae_of_all _ fv_Ag) (ae_of_all _ fv_Ag)
    (ae_of_all _ lim_Ag) (ae_of_all _ lim_Ag)

/-- The model-level càdlàg corollary, instantiated in the Gaussian model. -/
example : ∀ᵐ ω ∂(gaussianReal 0 1), ∀ t, Ag t ω = Ag t ω :=
  ae_forall_eq_compensator_cadlag measurable_id measurable_const hind_g
    (martingale_compensatedProcess measurable_id measurable_const hind_g)
    (measurable_compensator_strictPast measurable_id measurable_const _)
    continuousWithinAt_Ag (ae_of_all _ fv_Ag) (ae_of_all _ lim_Ag)

/-- The hazard measure of the standard Gaussian charges `(-∞, 0]`. -/
theorem hazard_gaussian_Iic_zero_ne_zero :
    hazardMeasure ((gaussianReal 0 1).map id) (Iic 0) ≠ 0 := by
  rw [Measure.map_id, hazardMeasure, withDensity_apply _ measurableSet_Iic]
  intro h
  have h1 : ∫⁻ _ in Iic (0 : ℝ), (1 : ℝ≥0∞) ∂gaussianReal 0 1 ≤
      ∫⁻ s in Iic 0, (gaussianReal 0 1 (Ici s))⁻¹ ∂gaussianReal 0 1 :=
    setLIntegral_mono' measurableSet_Iic fun _ _ => ENNReal.one_le_inv.2 prob_le_one
  rw [h, setLIntegral_const, one_mul, nonpos_iff_eq_zero] at h1
  have := gaussianReal_absolutelyContinuous' 0 one_ne_zero h1
  simp [Real.volume_Iic] at this

theorem Ag_zero_pos {ω : ℝ} (hω : 0 ≤ ω) : 0 < Ag 0 ω := by
  rw [compensator_eq, min_eq_left (show (0 : ℝ) ≤ Xg ω from le_min hω zero_le_one)]
  exact ENNReal.toReal_pos hazard_gaussian_Iic_zero_ne_zero (hazard_gaussian_Iic_ne_top 0)

/-- **The theorem has content.** `N - 2A` is not a martingale: `2A` is predictable, càdlàg, of
finite variation and normalized, so `ae_forall_eq_compensator_cadlag` (which does not use that
`2A` is stopped) would force `2A = A` almost surely, contradicting `A(0) > 0` on `{ω ≥ 0}`. -/
example : ¬ Martingale (fun t => countingProcess id (fun _ : ℝ => (1 : ℝ)) t - fun ω => 2 * Ag t ω)
    ℱg (gaussianReal 0 1) := by
  intro hM
  have h := ae_forall_eq_compensator_cadlag measurable_id measurable_const hind_g hM
    (fun t => (measurable_compensator_strictPast measurable_id measurable_const _ t).const_mul 2)
    (fun ω t => continuousWithinAt_const.mul (continuousWithinAt_Ag ω t))
    (ae_of_all _ fun _ => (((monotone_compensator (hazard_gaussian_Iic_ne_top _)).const_mul
      (by norm_num : (0 : ℝ) ≤ 2)).monotoneOn univ).locallyBoundedVariationOn)
    (ae_of_all _ fun ω => by simpa using (lim_Ag ω).const_mul 2)
  have hsub : Ici (0 : ℝ) ⊆ {ω | ¬ ∀ t, 2 * Ag t ω = Ag t ω} := fun ω (hω : 0 ≤ ω) h' => by
    have h0 := h' 0
    have := Ag_zero_pos hω
    linarith
  exact gaussianReal_Ici_ne_zero 0 (measure_mono_null hsub (ae_iff.1 h))

/-! ### Beyond the stopped theorem: a càdlàg compensator that is not stopped at exit -/

/-- A jump of size `1` at time `1` on the null event `{X = 0}` (that is, `ω = 0`). -/
noncomputable def bump (t ω : ℝ) : ℝ := if Xg ω = 0 ∧ 1 ≤ t then 1 else 0

/-- The competitor `A' = A + bump`. -/
noncomputable def Ab (t ω : ℝ) : ℝ := Ag t ω + bump t ω

theorem measurable_bump_strictPast (t : ℝ) : Measurable[⨆ s < t, ℱg s] (bump t) := by
  by_cases ht : 1 ≤ t
  · have hset : {ω : ℝ | Xg ω = 0 ∧ 1 ≤ t} = (fun ω => min t (Xg ω)) ⁻¹' {0} := by
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, ht, and_true]
      constructor
      · intro h; rw [h, min_eq_right (by linarith)]
      · intro h
        rcases min_choice t (Xg ω) with h' | h'
        · rw [h'] at h; linarith
        · rwa [h'] at h
    have hm : MeasurableSet[⨆ s < t, ℱg s] {ω : ℝ | Xg ω = 0 ∧ 1 ≤ t} := by
      rw [hset]
      exact measurable_min_obsTime_strictPast measurable_id measurable_const t
        (measurableSet_singleton 0)
    exact Measurable.ite hm measurable_const measurable_const
  · have : bump t = fun _ => 0 := funext fun ω => by simp [bump, ht]
    rw [this]; exact measurable_const

theorem continuousWithinAt_bump (ω t : ℝ) :
    ContinuousWithinAt (fun s => bump s ω) (Ici t) t := by
  have key : ∀ᶠ s in 𝓝[≥] t, bump s ω = bump t ω := by
    by_cases hX : Xg ω = 0
    · by_cases ht : 1 ≤ t
      · filter_upwards [self_mem_nhdsWithin] with s (hs : t ≤ s)
        simp [bump, hX, ht, ht.trans hs]
      · filter_upwards [Ico_mem_nhdsGE (not_le.1 ht)] with s hs
        simp [bump, hX, not_le.2 hs.2, ht]
    · filter_upwards with s
      simp [bump, hX]
  exact continuousWithinAt_const.congr_of_eventuallyEq key rfl

/-- `bump` vanishes off `{ω = 0}`. -/
theorem bump_eq_zero {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) : bump t ω = 0 := by
  have hX : Xg ω ≠ 0 := fun h => by
    simp only [obsTime, id] at h
    rcases min_choice ω 1 with h' | h'
    · exact hω (h' ▸ h)
    · rw [h'] at h; norm_num at h
  simp [bump, hX]

theorem ae_ne_zero : ∀ᵐ ω ∂(gaussianReal 0 1), ω ≠ 0 := by
  have : gaussianReal 0 1 {0} = 0 := by
    have h := gaussianReal_absolutelyContinuous 0 one_ne_zero
    exact h (Real.volume_singleton)
  exact compl_mem_ae_iff.2 this

/-- `A'` is a compensator: `N - A'` agrees with `N - A` off the null event `{ω = 0}`, along whole
paths, and is adapted. -/
theorem martingale_Ab :
    Martingale (fun t => countingProcess id (fun _ : ℝ => (1 : ℝ)) t - Ab t) ℱg
      (gaussianReal 0 1) := by
  have hM := martingale_compensatedProcess measurable_id measurable_const hind_g
    (μ := gaussianReal 0 1)
  have heq : ∀ t, compensatedProcess id (fun _ : ℝ => (1 : ℝ))
      (hazardMeasure ((gaussianReal 0 1).map id)) t =ᵐ[gaussianReal 0 1]
        countingProcess id (fun _ : ℝ => (1 : ℝ)) t - Ab t := fun t =>
    ae_ne_zero.mono fun ω hω => by
      simp only [compensatedProcess, Pi.sub_apply, Ab, bump_eq_zero hω, add_zero]
  refine ⟨fun t => ?_, fun i j hij =>
    (condExp_congr_ae (heq j)).symm.trans ((hM.condExp_ae_eq hij).trans (heq i))⟩
  have hA : Measurable[ℱg t] (Ab t) :=
    ((measurable_compensator_strictPast measurable_id measurable_const _ t).add
      (measurable_bump_strictPast t)).mono
      (strictPast_le_history measurable_id measurable_const t) le_rfl
  exact ((measurable_countingProcess_history measurable_id measurable_const le_rfl).sub
    hA).stronglyMeasurable

/-- **`A'` is not stopped at exit**, so the merged `ae_forall_eq_compensator` does not apply to
it: at `ω = 0` (exit at `X = 0`), `A'(1) = A(0) + 1` while `A'(1 ∧ X) = A'(0) = A(0)`. -/
theorem not_stopped_Ab : ¬ ∀ t ω, Ab t ω = Ab (min t (Xg ω)) ω := by
  intro h
  have hX : Xg 0 = 0 := by simp [obsTime]
  have h1 := h 1 0
  rw [hX, min_eq_right zero_le_one] at h1
  have hA : Ag 1 0 = Ag 0 0 := by
    rw [compensator_min_obsTime, hX, min_eq_right zero_le_one]
  simp only [Ab, bump, hX, le_refl, and_self, ite_true] at h1
  simp only [Measure.map_id] at hA h1
  norm_num at h1
  linarith

/-- **The càdlàg theorem applies to `A'`**: it is predictable, càdlàg, of finite variation and
normalized, so `ae_forall_eq_compensator_cadlag` identifies it with `A` almost surely, although
it is not stopped at exit. -/
example : ∀ᵐ ω ∂(gaussianReal 0 1), ∀ t, Ab t ω =
    compensator id (fun _ : ℝ => (1 : ℝ)) (hazardMeasure ((gaussianReal 0 1).map id)) t ω :=
  ae_forall_eq_compensator_cadlag measurable_id measurable_const hind_g martingale_Ab
    (fun t => (measurable_compensator_strictPast measurable_id measurable_const _ t).add
      (measurable_bump_strictPast t))
    (fun ω t => (continuousWithinAt_Ag ω t).add (continuousWithinAt_bump ω t))
    (ae_ne_zero.mono fun ω hω => by
      have : (fun t => Ab t ω) = fun t => Ag t ω := funext fun t => by
        simp [Ab, bump_eq_zero hω]
      rw [this]; exact fv_Ag ω)
    (ae_ne_zero.mono fun ω hω => by
      have : (fun t => Ab t ω) = fun t => Ag t ω := funext fun t => by
        simp [Ab, bump_eq_zero hω]
      rw [this]; exact lim_Ag ω)

end MathlibExtTest.Probability.Statistics.CompensatorUniquenessCadlag
