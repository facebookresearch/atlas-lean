/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.KMRemainderContinuous

@[expose] public section

open MeasureTheory Set Real ProbabilityTheory
open MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime
open MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime.ExpCensoredAtOne

namespace MathlibExtTest.Probability.Statistics.KMRemainderContinuous

/-! ### The one-subject estimator, from the grouped-data definition -/

/-- A subject failing at time `2`, censoring at `3`: `Ŝ = 1` before `2` and `0` from `2` on,
computed from `CensoredData.kmSurvival`, not from `kaplanMeierOne_eq`. -/
example : kaplanMeierOne (fun _ : Unit => (2 : ℝ)) (fun _ => 3) 1 () = 1 ∧
    kaplanMeierOne (fun _ : Unit => (2 : ℝ)) (fun _ => 3) 2 () = 0 := by
  constructor <;>
    norm_num [kaplanMeierOne, oneSubjectData, CensoredData.kmSurvival, CensoredData.kmFactor,
      CensoredData.atRisk, obsTime, Finset.filter_true_of_mem]

/-- Censored at `2` before the failure at `3`: `Ŝ` stays `1` forever. -/
example : kaplanMeierOne (fun _ : Unit => (3 : ℝ)) (fun _ => 2) 5 () = 1 := by
  norm_num [kaplanMeierOne, oneSubjectData, CensoredData.kmSurvival, CensoredData.kmFactor,
    CensoredData.atRisk, obsTime]

/-- The left limit at the failure time is `1`, while the value there is `0` (a genuine jump). -/
example : kaplanMeierOneLeft (fun _ : Unit => (2 : ℝ)) (fun _ => 3) 2 () = 1 := by
  norm_num [kaplanMeierOneLeft]

/-- `dN` puts mass `1` on `(0, 2]` for a failure at `2`, and none for a censored subject. -/
example : (countingMeasure (fun _ : Unit => (2 : ℝ)) (fun _ => 3) ()).real (Ioc 0 2) = 1 ∧
    (countingMeasure (fun _ : Unit => (3 : ℝ)) (fun _ => 2) ()).real (Ioc 0 5) = 0 := by
  constructor <;> norm_num [countingMeasure, Measure.real]

/-! ### Boundary cases computed from the definition of `kmRemainder` -/

/-- Zero hazard, zero remainder (whatever the censoring). -/
example (T C : Unit → ℝ) (S : ℝ → ℝ) (t : ℝ) : kmRemainder T C S 0 t () = 0 := by
  simp [kmRemainder]

/-- At `t = 0` the integration domain `(0, 0]` is empty. -/
example (T C : Unit → ℝ) (S : ℝ → ℝ) (Λ : Measure ℝ) : kmRemainder T C S Λ 0 () = 0 := by
  simp [kmRemainder]

/-- An uncensored subject has no remainder, for any `S` and `Λ`. -/
example (S : ℝ → ℝ) (Λ : Measure ℝ) (t : ℝ) :
    kmRemainder (fun _ : Unit => (2 : ℝ)) (fun _ => 3) S Λ t () = 0 :=
  kmRemainder_eq_zero_of_le (by norm_num)

/-! ### The exponential model: hypotheses hold, values are nonzero -/

/-- The hazard measure of `Exp(1)` gives `(0, 1]` mass `1` (hazard rate `1`). -/
example : Λ₀ (Ioc 0 1) = 1 := by
  have h := congrArg (fun ν : Measure ℝ => ν (Ioc 0 1)) hazardMeasure_restrict_Ioi
  have hsub : Ioc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 := inter_eq_left.2 fun s hs => hs.1
  simp only [Measure.restrict_apply measurableSet_Ioc, hsub] at h
  rw [h]
  simp

/-- `Λ₀` restricted to `(0, b]` is Lebesgue measure there. -/
lemma Λ₀_restrict_Ioc {b : ℝ} : Λ₀.restrict (Ioc 0 b) = volume.restrict (Ioc 0 b) := by
  have hsub : Ioc (0 : ℝ) b ⊆ Ioi 0 := fun s hs => hs.1
  rw [← Measure.restrict_restrict_of_subset hsub, hazardMeasure_restrict_Ioi,
    Measure.restrict_restrict_of_subset hsub]

lemma S₀_antitone : Antitone S₀ := fun _ _ hab => exp_le_exp.2 (neg_le_neg hab)

/-- **`kmIntegrand` from its definition**: `H(s) = Ŝ(s-)/(S(s)Y(s))` is `e^{1/2}` at `s = 1/2`
(at risk, `Ŝ(s-) = 1`), and `0` at `s = 2` after censoring at `1` (`Y = 0`, Gill's `J = 0`). -/
example : kmIntegrand T₀ C₀ S₀ (1 / 2) 2 = exp (1 / 2) ∧ kmIntegrand T₀ C₀ S₀ 2 2 = 0 := by
  constructor
  · norm_num [kmIntegrand, kaplanMeierOneLeft, atRiskProcess, S₀, exp_neg]
  · norm_num [kmIntegrand, kaplanMeierOneLeft, atRiskProcess]

/-- **`kmRemainder_pos` applied** at `ω = 2` (censored at `1`), `t = 3`. -/
example : 0 < kmRemainder T₀ C₀ S₀ Λ₀ 3 2 :=
  kmRemainder_pos (by norm_num [obsTime]) (fun a b ha hab _ => volterra_hazard ha hab)
    (by norm_num) (by norm_num) (exp_pos _) (exp_lt_exp.2 (by norm_num))

/-- **`kmRemainder_nonneg` applied** at `ω = 2`, `t = 3`. -/
example : 0 ≤ kmRemainder T₀ C₀ S₀ Λ₀ 3 2 :=
  kmRemainder_nonneg (by norm_num [obsTime]) (fun a b ha hab _ => volterra_hazard ha hab)
    (exp_pos _) (S₀_antitone.antitoneOn _)

/-- **Non-vacuity of the representation.** For the subject `ω = 2` (censored at `1`), at `t = 3`
all hypotheses of `kaplanMeierOne_div_sub_one` hold, and its left side `e^3 - 1` (computed from
`kaplanMeierOne`) is nonzero. -/
example : kaplanMeierOne T₀ C₀ 3 2 / S₀ 3 - 1 =
      -kmMartingaleIntegral T₀ C₀ S₀ Λ₀ 3 2 + kmRemainder T₀ C₀ S₀ Λ₀ 3 2 ∧
    kaplanMeierOne T₀ C₀ 3 2 / S₀ 3 - 1 = exp 3 - 1 := by
  refine ⟨kaplanMeierOne_div_sub_one (by norm_num [obsTime]) (by norm_num) (by simp [S₀])
    fun a b ha hab _ => volterra_hazard ha hab, ?_⟩
  norm_num [kaplanMeierOne, oneSubjectData, CensoredData.kmSurvival, CensoredData.kmFactor,
    CensoredData.atRisk, obsTime, S₀, exp_neg]

/-- **The martingale term from its definition** (not through `kmMartingaleIntegral_eq`): the
censored subject `ω = 2` has `dN = 0`, and `∫_{(0, 3]} H Y dΛ = ∫_{(0, 1]} e^s ds = e - 1`, so the
martingale term is `-(e - 1)`. -/
example : kmMartingaleIntegral T₀ C₀ S₀ Λ₀ 3 2 = -(exp 1 - 1) := by
  have hN : countingMeasure T₀ C₀ 2 = 0 := by norm_num [countingMeasure]
  have hf : (fun s => kmIntegrand T₀ C₀ S₀ s 2 * atRiskProcess T₀ C₀ s 2) =
      (Iic 1).indicator fun s => exp s := by
    funext s
    by_cases hs : s ≤ 1
    · have h2 : s ≤ 2 := hs.trans one_le_two
      simp [kmIntegrand, kaplanMeierOneLeft, atRiskProcess, hs, h2, S₀, exp_neg]
    · simp [kmIntegrand, kaplanMeierOneLeft, atRiskProcess, hs]
  rw [kmMartingaleIntegral, hN, Measure.restrict_zero, integral_zero_measure, hf,
    setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic,
    min_eq_right (by norm_num : (1 : ℝ) ≤ 3),
    Λ₀_restrict_Ioc, ← intervalIntegral.integral_of_le zero_le_one, integral_exp, exp_zero]
  ring

/-- The remainder at `ω = 2`, `t = 3` is `e^3 - e`; with the martingale term `-(e - 1)` the
right side of the representation is `e^3 - 1`, matching the left side above. -/
example : kmRemainder T₀ C₀ S₀ Λ₀ 3 2 = exp 3 - exp 1 := by
  rw [kmRemainder_eq_indicator (by norm_num)]
  norm_num

/-- Boundary `t = 1` (the censoring time): the remainder is still `0` everywhere. -/
example : kmRemainder T₀ C₀ S₀ Λ₀ 1 = 0 := by
  rw [kmRemainder_eq_indicator le_rfl]
  funext ω
  simp

/-- **Mean bias computed from the definitions** at `t = 2`, without the representation:
`E[Ŝ(2)/S(2)] - 1 = P(T > 1) e^2 - 1 = e - 1`. -/
example : ∫ ω, (kaplanMeierOne T₀ C₀ 2 ω / S₀ 2 - 1) ∂μ₀ = exp 1 - 1 := by
  have hfun : (fun ω => kaplanMeierOne T₀ C₀ 2 ω / S₀ 2 - 1) =
      fun ω => (Ioi 1).indicator (fun _ => exp 2) ω - 1 := by
    funext ω
    by_cases hω : 1 < ω
    · norm_num [kaplanMeierOne, oneSubjectData, CensoredData.kmSurvival, CensoredData.kmFactor,
        CensoredData.atRisk, obsTime, S₀, exp_neg, hω, hω.le, not_le.2 hω]
    · have hω' : ω ≤ 1 := not_lt.1 hω
      norm_num [kaplanMeierOne, oneSubjectData, CensoredData.kmSurvival, CensoredData.kmFactor,
        CensoredData.atRisk, obsTime, S₀, hω, hω', min_eq_left hω', hω'.trans one_le_two,
        Finset.filter_true_of_mem]
  rw [hfun, integral_sub ((integrable_const _).indicator measurableSet_Ioi) (integrable_const _),
    integral_indicator_const _ measurableSet_Ioi, measureReal_Ioi zero_le_one, integral_const,
    probReal_univ, smul_eq_mul, smul_eq_mul, mul_one, ← exp_add]
  norm_num

/-- **The general mean-bias theorem applies to the model**: all hypotheses of
`integral_kaplanMeierOne_div_sub_one` hold (`T ⊥ C` since `C` is constant, `X > 0` a.s.), and it
returns the value `e - 1` computed from the definitions in the previous example. -/
example : ∫ ω, (kaplanMeierOne T₀ C₀ 2 ω / S₀ 2 - 1) ∂μ₀ = exp 1 - 1 := by
  have hmap : μ₀.map T₀ = μ₀ := Measure.map_id
  have hIic : μ₀ (Iic 0) = 0 := by
    have h := measureReal_compl (μ := μ₀) (measurableSet_Ioi (a := (0 : ℝ)))
    rw [compl_Ioi, measureReal_Ioi le_rfl, probReal_univ, neg_zero, exp_zero, sub_self] at h
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h
  have hX : ∀ᵐ ω ∂μ₀, 0 < obsTime T₀ C₀ ω := by
    refine ae_iff.2 (measure_mono_null (fun ω (hω : ¬ 0 < min ω 1) => ?_) hIic)
    rw [lt_min_iff, not_and_or] at hω
    rcases hω with h | h
    · exact not_lt.1 h
    · exact absurd zero_lt_one h
  have hint : IntegrableOn (fun s => (S₀ s)⁻¹) (Ioc 0 2) (hazardMeasure (μ₀.map T₀)) := by
    rw [hmap, IntegrableOn, Λ₀_restrict_Ioc]
    simp only [S₀, exp_neg, inv_inv]
    exact continuous_exp.integrableOn_Ioc
  have hind : IndepFun T₀ C₀ μ₀ := indepFun_const_right T₀ (1 : ℝ)
  rw [integral_kaplanMeierOne_div_sub_one (μ := μ₀) (T := T₀) (C := C₀) (S := S₀) measurable_id
    measurable_const hind zero_le_two (by simp [S₀]) S₀_antitone (exp_pos _) hint
    (fun a b ha hab _ => by rw [hmap]; exact volterra_hazard ha hab) hX, hmap,
    integral_kmRemainder one_le_two]
  norm_num

/-- The mean remainder at `t = 2` is the same `e - 1`. -/
example : ∫ ω, kmRemainder T₀ C₀ S₀ Λ₀ 2 ω ∂μ₀ = exp 1 - 1 := by
  rw [integral_kmRemainder one_le_two]
  norm_num

/-- The remainder is positive on the censored event `{T > 1}`, of probability `e^{-1} > 0`. -/
example : 0 < kmRemainder T₀ C₀ S₀ Λ₀ 2 3 ∧ 0 < μ₀.real (Ioi 1) := by
  refine ⟨?_, by rw [measureReal_Ioi zero_le_one]; exact exp_pos _⟩
  rw [kmRemainder_eq_indicator one_le_two]
  norm_num

/-- `E[R(2) | ℱ₁]` is not a.e. zero. -/
example : ¬ μ₀[kmRemainder T₀ C₀ S₀ Λ₀ 2 | ℱ₀ 1] =ᵐ[μ₀] 0 :=
  condExp_kmRemainder_ne_zero one_lt_two

end MathlibExtTest.Probability.Statistics.KMRemainderContinuous
