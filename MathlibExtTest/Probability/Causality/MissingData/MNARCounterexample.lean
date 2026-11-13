/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.MNARCounterexample

/-!
# Tests for the MNAR nonidentification counterexample

* The δ-shift and the stratum shift on concrete points, including the identity case off the
  shifted stratum.
* The general nonidentification theorems instantiated at `constOutcomeLaw` (nonresponse
  probability `1/2`), the explicit pair, and mean imputation on both laws.
* Boundary, no respondents: two point masses on nonrespondents with different outcomes share
  their observed-data law.
* Boundary, positivity failure: a law on `Bool × Bool × ℝ` that satisfies `CondIndepDiscrete`
  given the covariate but has no respondents in the stratum `x = false`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality
  MathlibExt.Probability.Causality.MissingData

namespace MathlibExtTest.Probability.Causality.MissingData

open scoped Classical in
/-- The value of a half-half mixture of two point masses on a set. -/
lemma measureReal_half_dirac_add {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Set α) (a b : α) :
    ((2⁻¹ : ENNReal) • (Measure.dirac a + Measure.dirac b)).real s =
      ((if a ∈ s then 1 else 0) + (if b ∈ s then 1 else 0)) / 2 := by
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;>
    simp [Measure.real, Measure.dirac_apply, ha, hb, ENNReal.toReal_inv,
      ENNReal.inv_two_add_inv_two]

/-- Every real function is integrable against a half-half mixture of two point masses. -/
lemma integrable_half_dirac_add {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → ℝ) (a b : α) :
    Integrable f ((2⁻¹ : ENNReal) • (Measure.dirac a + Measure.dirac b)) :=
  ((integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top)).smul_measure
    (by simp)

/-! ### The δ-shift -/

example : nonresponseShift 2 (true, 5) = (true, 5) := by simp [nonresponseShift]

example : nonresponseShift 2 (false, 5) = (false, 7) := by
  simp [nonresponseShift]; norm_num

lemma constOutcomeLaw_real_nonresponse : constOutcomeLaw.real {z | z.1 = false} = 1 / 2 := by
  rw [constOutcomeLaw, measureReal_half_dirac_add]; norm_num

/-- Shifting the nonrespondents of `constOutcomeLaw` by `δ` moves the mean from `1` to
`1 + δ / 2` and keeps the observed-data law. -/
example (δ : ℝ) :
    ∫ z, z.2 ∂(constOutcomeLaw.map (nonresponseShift δ)) = 1 + δ / 2 := by
  rw [integral_snd_map_nonresponseShift (integrable_of_integral_eq_one
      integral_snd_constOutcomeLaw) δ,
    integral_snd_constOutcomeLaw, constOutcomeLaw_real_nonresponse]
  ring

example (δ : ℝ) :
    (constOutcomeLaw.map (nonresponseShift δ)).map
        (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) =
      constOutcomeLaw.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) :=
  map_obsRY_map_nonresponseShift _ δ

/-! ### Nonidentification at a concrete law -/

lemma integrable_snd_constOutcomeLaw : Integrable Prod.snd constOutcomeLaw :=
  integrable_of_integral_eq_one integral_snd_constOutcomeLaw

/-- The hypotheses of the general theorem are satisfiable: at `constOutcomeLaw` the mean `42`
is compatible with the observed data. -/
example : ∃ Q : Measure (Bool × ℝ), IsProbabilityMeasure Q ∧ Integrable Prod.snd Q ∧
    Q.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) =
      constOutcomeLaw.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) ∧
    ∫ z, z.2 ∂Q = 42 :=
  exists_map_obsRY_eq_integral_eq integrable_snd_constOutcomeLaw
    (by rw [constOutcomeLaw_real_nonresponse]; norm_num) 42

/-- The functional "respondents' mean" fails at some law with the observed data of
`constOutcomeLaw`. -/
example : ∃ Q : Measure (Bool × ℝ), IsProbabilityMeasure Q ∧ Integrable Prod.snd Q ∧
    Q.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) =
      constOutcomeLaw.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) ∧
    (fun O : Measure (Bool × ℝ) => (∫ w in {w | w.1 = true}, w.2 ∂O) /
        O.real {w | w.1 = true})
      (Q.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ)))) ≠ ∫ z, z.2 ∂Q :=
  exists_map_obsRY_eq_integral_ne integrable_snd_constOutcomeLaw
    (by rw [constOutcomeLaw_real_nonresponse]; norm_num)
    (fun O => (∫ w in {w | w.1 = true}, w.2 ∂O) / O.real {w | w.1 = true})

/-- No functional of the observed-data law identifies the mean even among the laws with the
observed data of `constOutcomeLaw`: otherwise `constOutcomeLaw` would have no nonresponse. -/
example (F : Measure (Bool × ℝ) → ℝ) :
    ¬ ∀ Q : Measure (Bool × ℝ), IsProbabilityMeasure Q → Integrable Prod.snd Q →
      Q.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) =
        constOutcomeLaw.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) →
      F (Q.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ)))) = ∫ z, z.2 ∂Q := by
  intro hF
  have := measureReal_nonresponse_eq_zero_of_identifies F integrable_snd_constOutcomeLaw hF
  rw [constOutcomeLaw_real_nonresponse] at this
  norm_num at this

/-! ### The explicit pair and mean imputation -/

example : ∫ z, z.2 ∂constOutcomeLaw ≠ ∫ z, z.2 ∂selfMaskingLaw :=
  constOutcomeLaw_selfMaskingLaw_nonidentified.2

example : CondIndepDiscrete constOutcomeLaw {z | z.1 = true} Prod.snd (fun _ => ()) :=
  condIndepDiscrete_constOutcomeLaw

example : ¬ CondIndepDiscrete selfMaskingLaw {z | z.1 = true} Prod.snd (fun _ => ()) :=
  not_condIndepDiscrete_selfMaskingLaw

lemma integrable_snd_selfMaskingLaw : Integrable Prod.snd selfMaskingLaw :=
  integrable_half_dirac_add _ _ _

/-- The respondents' mean of `selfMaskingLaw` read off its observed-data law. -/
example : (∫ w in {w | w.1 = true}, w.2 ∂(selfMaskingLaw.map
      (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))))) /
    (selfMaskingLaw.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ)))).real
      {w | w.1 = true} = 1 := by
  rw [← respondentMean_map_obsRY, respondentMean_selfMaskingLaw.1]

/-- Mean imputation fails at some law with the observed data of `constOutcomeLaw`. -/
example : ∃ Q : Measure (Bool × ℝ), IsProbabilityMeasure Q ∧ Integrable Prod.snd Q ∧
    Q.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) =
      constOutcomeLaw.map (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) ∧
    Q.real {z | z.1 = true} ≠ 0 ∧
    (∫ w in {w | w.1 = true}, w.2 ∂Q) / Q.real {w | w.1 = true} ≠ ∫ z, z.2 ∂Q :=
  exists_map_obsRY_eq_respondentMean_ne integrable_snd_constOutcomeLaw
    (by rw [constOutcomeLaw_real_nonresponse]; norm_num)
    (by rw [constOutcomeLaw, measureReal_half_dirac_add]; norm_num)

/-- Mean imputation on `selfMaskingLaw` yields `1`, while the full-data mean is `1 / 2`. -/
example : ∫ z, (if z.1 then z.2 else
      (∫ w in {w | w.1 = true}, w.2 ∂selfMaskingLaw) / selfMaskingLaw.real {w | w.1 = true})
      ∂selfMaskingLaw ≠ ∫ z, z.2 ∂selfMaskingLaw := by
  have hR : selfMaskingLaw.real {w : Bool × ℝ | w.1 = true} ≠ 0 := by
    rw [selfMaskingLaw, measureReal_half_dirac_add]; norm_num
  rw [integral_ite_respondentMean integrable_snd_selfMaskingLaw hR,
    respondentMean_selfMaskingLaw.1, respondentMean_selfMaskingLaw.2]
  norm_num

/-! ### Boundary: no respondents -/

example : (Measure.dirac ((false, 3) : Bool × ℝ)).map
      (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) =
    (Measure.dirac ((false, -7) : Bool × ℝ)).map
      (fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))) :=
  map_obsRY_eq_of_measure_response_eq_zero (by simp [Measure.dirac_apply])
    (by simp [Measure.dirac_apply])

/-! ### Boundary: positivity failure under MAR -/

example : stratumShift true 3 (false, false, 1) = (false, false, 1) :=
  stratumShift_of_ne 3 (by decide)

example : stratumShift false 3 (false, false, 1) = (false, false, 4) := by
  simp [stratumShift]; norm_num

example : stratumShift false 3 (false, true, 1) = (false, true, 1) := by
  simp [stratumShift]

/-- Covariate `X` a fair coin, response exactly when `X = true`, outcome `Y = 0`. Response is
conditionally independent of the outcome given `X`, but the stratum `X = false` has no
respondents. -/
noncomputable def positivityFailureLaw : Measure (Bool × Bool × ℝ) :=
  (2⁻¹ : ENNReal) • (Measure.dirac (true, true, 0) + Measure.dirac (false, false, 0))

instance : IsProbabilityMeasure positivityFailureLaw := by
  constructor
  simp [positivityFailureLaw, ENNReal.inv_two_add_inv_two]

lemma integrable_positivityFailureLaw : Integrable (fun z => z.2.2) positivityFailureLaw :=
  integrable_half_dirac_add _ _ _

lemma condIndepDiscrete_positivityFailureLaw :
    CondIndepDiscrete positivityFailureLaw {z | z.2.1 = true} (fun z => z.2.2) Prod.fst := by
  intro B _ w
  simp only [positivityFailureLaw, measureReal_half_dirac_add]
  by_cases h0 : (0 : ℝ) ∈ B <;> cases w <;> simp [h0]

example (t : ℝ) : ∃ Q : Measure (Bool × Bool × ℝ), IsProbabilityMeasure Q ∧
    Integrable (fun z => z.2.2) Q ∧
    CondIndepDiscrete Q {z | z.2.1 = true} (fun z => z.2.2) Prod.fst ∧
    Q.map (fun z : Bool × Bool × ℝ => (z.1, z.2.1, if z.2.1 then z.2.2 else (0 : ℝ))) =
      positivityFailureLaw.map
        (fun z : Bool × Bool × ℝ => (z.1, z.2.1, if z.2.1 then z.2.2 else (0 : ℝ))) ∧
    ∫ z, z.2.2 ∂Q = t := by
  refine exists_condIndepDiscrete_map_obsXRY_eq_integral_eq (x₀ := false)
    integrable_positivityFailureLaw condIndepDiscrete_positivityFailureLaw ?_ ?_ t
  · simp [positivityFailureLaw, Measure.dirac_apply]
  · rw [positivityFailureLaw, measureReal_half_dirac_add]; norm_num

end MathlibExtTest.Probability.Causality.MissingData
