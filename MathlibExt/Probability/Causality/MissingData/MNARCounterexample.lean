/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Missing not at random: the full-data mean is not identified

An outcome `Y` is missing for nonrespondents. With response indicator `R`, the *full data* are
`(R, Y)` and the *observed data* are `R` together with `Y` on `{R = true}`; below the observed data
of `(r, y)` are encoded as `(r, if r then y else 0)`. The target is the full-data mean `E[Y]`.
Without a model for how `R` depends on `Y` (missing not at random, MNAR, left unmodeled), the
observed-data law does not determine `E[Y]`. Full-data laws live on `Bool × ℝ`, and on
`𝒳 × Bool × ℝ` when there is an always-observed covariate.

## Main definitions

* `nonresponseShift δ`: add `δ` to the outcome of every nonrespondent (the δ-adjustment of
  pattern-mixture sensitivity analysis).
* `constOutcomeLaw`, `selfMaskingLaw`: two explicit full-data laws with a fair-coin response; the
  first has `Y = 1`, the second has `Y = 1` exactly on response (self-masking MNAR).
* `stratumShift x₀ c`: add `c` to the outcome of the nonrespondents in the covariate stratum
  `x = x₀`.

## Main results

* `exists_map_obsRY_eq_integral_eq`: if `P(R = false) > 0`, every real number is the mean of a
  full-data law with the given observed-data law (the identified set is `ℝ`).
* `exists_map_obsRY_eq_integral_ne`, `measureReal_nonresponse_eq_zero_of_identifies`: no
  functional of the observed-data law recovers the mean at any law with nonresponse.
* `constOutcomeLaw_selfMaskingLaw_nonidentified`: the explicit pair has the same observed-data law
  and means `1` and `1 / 2`; `condIndepDiscrete_constOutcomeLaw` and
  `not_condIndepDiscrete_selfMaskingLaw` show that response is independent of the outcome under the
  first law and not under the second.
* Summary-statistic imputation: `integral_ite_respondentMean` (filling the missing outcomes with
  the respondents' mean yields that mean back) and `respondentMean_selfMaskingLaw` (on the
  self-masking law it gives `1`, the full-data mean is `1 / 2`). The imputed value is a functional
  of the observed-data law, so by `exists_map_obsRY_eq_integral_ne` it identifies nothing without
  an assumption on the nonresponse mechanism.
* Boundary, no respondents: `map_obsRY_eq_dirac_of_measure_response_eq_zero` (the observed-data
  law is `δ_(false, 0)` whatever the outcome law).
* Boundary, positivity failure: `exists_condIndepDiscrete_map_obsXRY_eq_integral_eq`. Even when
  response is conditionally independent of the outcome given the covariate (`CondIndepDiscrete`,
  i.e. missingness at random), a covariate stratum of positive probability with no respondents
  leaves the mean unidentified.

## Implementation notes

The observed-data map and the MCAR / MAR predicates belong to the missing-data definitions file,
which this file does not import; the observed-data map is written out as a local notation, and
independence statements use `CondIndepDiscrete` from `CausalIdentification` directly.

## References

* D. B. Rubin, *Inference and missing data*, Biometrika 63(3) (1976), 581–592.
* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley
  (2019), Chapters 1, 4 and 15.
* C. F. Manski, *Partial Identification of Probability Distributions*, Springer (2003),
  Chapter 1.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality.MissingData

open MeasureTheory ProbabilityTheory

-- The observed data of a full-data point `(r, y)`: the response indicator `r` and the outcome
-- `y` when `r` holds, the placeholder `0` otherwise. Written out (as a local notation) rather than
-- defined, since the observed-data map belongs to the missing-data definitions file.
set_option quotPrecheck false in
local notation "obsRY" => fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))

lemma measurable_obsRY : Measurable obsRY :=
  measurable_fst.prodMk (Measurable.ite (p := {z : Bool × ℝ | z.1 = true})
    (measurable_fst (measurableSet_singleton true)) measurable_snd measurable_const)

/-! ### The δ-shift of nonrespondents -/

lemma measurableSet_nonresponse : MeasurableSet {z : Bool × ℝ | z.1 = false} :=
  measurable_fst (measurableSet_singleton false)

/-- The δ-shift of nonrespondents: `(r, y) ↦ (r, y)` if `r`, and `(r, y + δ)` otherwise. Pushing
a full-data law forward along it changes the outcome law of the nonrespondents only; this is the
δ-adjustment of pattern-mixture sensitivity analysis. -/
noncomputable def nonresponseShift (δ : ℝ) (z : Bool × ℝ) : Bool × ℝ :=
  (z.1, z.2 + {z : Bool × ℝ | z.1 = false}.indicator (fun _ => δ) z)

lemma measurable_nonresponseShift (δ : ℝ) : Measurable (nonresponseShift δ) :=
  measurable_fst.prodMk (measurable_snd.add (measurable_const.indicator measurableSet_nonresponse))

/-- The δ-shift does not change the observed data. -/
lemma obsRY_nonresponseShift (δ : ℝ) (z : Bool × ℝ) :
    (obsRY) (nonresponseShift δ z) = (obsRY) z := by
  rcases z with ⟨_ | _, y⟩ <;> simp [nonresponseShift]

/-- The δ-shift does not change the observed-data law. -/
theorem map_obsRY_map_nonresponseShift (P : Measure (Bool × ℝ)) (δ : ℝ) :
    (P.map (nonresponseShift δ)).map obsRY = P.map obsRY := by
  rw [Measure.map_map measurable_obsRY (measurable_nonresponseShift δ)]
  exact congrArg (fun f => P.map f) (funext (obsRY_nonresponseShift δ))

lemma integrable_snd_map_nonresponseShift {P : Measure (Bool × ℝ)} [IsFiniteMeasure P]
    (hP : Integrable Prod.snd P) (δ : ℝ) : Integrable Prod.snd (P.map (nonresponseShift δ)) :=
  (integrable_map_measure measurable_snd.aestronglyMeasurable
    (measurable_nonresponseShift δ).aemeasurable).2
    (hP.add ((integrable_const δ).indicator measurableSet_nonresponse))

/-- The δ-shift moves the full-data mean by `δ P(R = false)`. -/
theorem integral_snd_map_nonresponseShift {P : Measure (Bool × ℝ)} [IsFiniteMeasure P]
    (hP : Integrable Prod.snd P) (δ : ℝ) :
    ∫ z, z.2 ∂(P.map (nonresponseShift δ)) =
      ∫ z, z.2 ∂P + δ * P.real {z | z.1 = false} := by
  rw [integral_map (measurable_nonresponseShift δ).aemeasurable
    measurable_snd.aestronglyMeasurable]
  simp only [nonresponseShift]
  rw [integral_add hP ((integrable_const δ).indicator measurableSet_nonresponse),
    integral_indicator_const _ measurableSet_nonresponse, smul_eq_mul, mul_comm]

/-! ### Unmodeled MNAR: the full-data mean is not identified -/

/-- **The identified set of the mean is all of `ℝ`.** If nonresponse has positive probability,
every real number is the outcome mean of a full-data law with the same observed-data law. -/
theorem exists_map_obsRY_eq_integral_eq {P : Measure (Bool × ℝ)} [IsProbabilityMeasure P]
    (hP : Integrable Prod.snd P) (hR : P.real {z | z.1 = false} ≠ 0) (t : ℝ) :
    ∃ Q : Measure (Bool × ℝ), IsProbabilityMeasure Q ∧ Integrable Prod.snd Q ∧
      Q.map obsRY = P.map obsRY ∧ ∫ z, z.2 ∂Q = t := by
  set δ := (t - ∫ z, z.2 ∂P) / P.real {z | z.1 = false}
  refine ⟨P.map (nonresponseShift δ), inferInstance,
    integrable_snd_map_nonresponseShift hP δ, map_obsRY_map_nonresponseShift P δ, ?_⟩
  rw [integral_snd_map_nonresponseShift hP δ, div_mul_cancel₀ _ hR]
  ring

/-- **Nonidentification of the mean under unmodeled MNAR.** No functional `F` of the observed-data
law recovers the full-data mean at a law with positive nonresponse probability: some full-data
law with the same observed-data law has a different mean. Imputing the missing outcomes from a
summary statistic of the respondents (their mean or their median) is such a functional,
so it is a modelling assumption, not an identification. -/
theorem exists_map_obsRY_eq_integral_ne {P : Measure (Bool × ℝ)} [IsProbabilityMeasure P]
    (hP : Integrable Prod.snd P) (hR : P.real {z | z.1 = false} ≠ 0)
    (F : Measure (Bool × ℝ) → ℝ) :
    ∃ Q : Measure (Bool × ℝ), IsProbabilityMeasure Q ∧ Integrable Prod.snd Q ∧
      Q.map obsRY = P.map obsRY ∧ F (Q.map obsRY) ≠ ∫ z, z.2 ∂Q := by
  obtain ⟨Q, hQ, hQi, hobs, hmean⟩ := exists_map_obsRY_eq_integral_eq hP hR (F (P.map obsRY) + 1)
  exact ⟨Q, hQ, hQi, hobs, by rw [hobs, hmean]; linarith⟩

/-- **Identification forces full response.** If a functional `F` of the observed-data law equals
the full-data mean for every integrable full-data law, then every such law has nonresponse
probability `0`; contrapositively, without a model for the nonresponse mechanism, the mean is
identified at no law with positive nonresponse probability. -/
theorem measureReal_nonresponse_eq_zero_of_identifies (F : Measure (Bool × ℝ) → ℝ)
    (hF : ∀ Q : Measure (Bool × ℝ), IsProbabilityMeasure Q → Integrable Prod.snd Q →
      F (Q.map obsRY) = ∫ z, z.2 ∂Q)
    {P : Measure (Bool × ℝ)} [IsProbabilityMeasure P] (hP : Integrable Prod.snd P) :
    P.real {z | z.1 = false} = 0 := by
  by_contra hR
  obtain ⟨Q, hQ, hQi, -, hne⟩ := exists_map_obsRY_eq_integral_ne hP hR F
  exact hne (hF Q hQ hQi)

/-! ### An explicit pair of full-data laws -/

/-- A full-data law under which the response is independent of the outcome: `R` is a fair coin
and `Y = 1`. -/
noncomputable def constOutcomeLaw : Measure (Bool × ℝ) :=
  (2⁻¹ : ENNReal) • (Measure.dirac (true, 1) + Measure.dirac (false, 1))

/-- A *self-masking* (MNAR) full-data law: `R` is a fair coin and `Y = 1` exactly on response,
so the nonrespondents are those with `Y = 0`. -/
noncomputable def selfMaskingLaw : Measure (Bool × ℝ) :=
  (2⁻¹ : ENNReal) • (Measure.dirac (true, 1) + Measure.dirac (false, 0))

instance : IsProbabilityMeasure constOutcomeLaw := by
  constructor
  simp [constOutcomeLaw, ENNReal.inv_two_add_inv_two]

instance : IsProbabilityMeasure selfMaskingLaw := by
  constructor
  simp [selfMaskingLaw, ENNReal.inv_two_add_inv_two]

/-- The two laws have the same observed-data law, `½ δ_(true, 1) + ½ δ_(false, 0)`. -/
theorem map_obsRY_constOutcomeLaw :
    constOutcomeLaw.map obsRY = selfMaskingLaw.map obsRY := by
  rw [constOutcomeLaw, selfMaskingLaw, Measure.map_smul, Measure.map_smul,
    Measure.map_add _ _ measurable_obsRY, Measure.map_add _ _ measurable_obsRY,
    Measure.map_dirac' measurable_obsRY, Measure.map_dirac' measurable_obsRY]
  · simp
  all_goals exact measurable_obsRY.aemeasurable

private lemma integral_half_dirac_add (f : Bool × ℝ → ℝ) (a b : Bool × ℝ) :
    ∫ z, f z ∂((2⁻¹ : ENNReal) • (Measure.dirac a + Measure.dirac b)) = (f a + f b) / 2 := by
  rw [integral_smul_measure, integral_add_measure (integrable_dirac enorm_lt_top)
    (integrable_dirac enorm_lt_top), integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]
  ring

open scoped Classical in
private lemma measureReal_half_dirac_add (s : Set (Bool × ℝ)) (a b : Bool × ℝ) :
    ((2⁻¹ : ENNReal) • (Measure.dirac a + Measure.dirac b)).real s =
      ((if a ∈ s then 1 else 0) + (if b ∈ s then 1 else 0)) / 2 := by
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;>
    simp [Measure.real, Measure.dirac_apply, ha, hb, ENNReal.toReal_inv,
      ENNReal.inv_two_add_inv_two]

/-- The outcome mean under `constOutcomeLaw` is `1`. -/
theorem integral_snd_constOutcomeLaw : ∫ z, z.2 ∂constOutcomeLaw = 1 := by
  rw [constOutcomeLaw, integral_half_dirac_add]
  norm_num

/-- The outcome mean under `selfMaskingLaw` is `1 / 2`. -/
theorem integral_snd_selfMaskingLaw : ∫ z, z.2 ∂selfMaskingLaw = 1 / 2 := by
  rw [selfMaskingLaw, integral_half_dirac_add]
  norm_num

/-- **Explicit nonidentifiability.** Two full-data laws with the same observed-data law and
different outcome means. -/
theorem constOutcomeLaw_selfMaskingLaw_nonidentified :
    constOutcomeLaw.map obsRY = selfMaskingLaw.map obsRY ∧
      ∫ z, z.2 ∂constOutcomeLaw ≠ ∫ z, z.2 ∂selfMaskingLaw := by
  refine ⟨map_obsRY_constOutcomeLaw, ?_⟩
  rw [integral_snd_constOutcomeLaw, integral_snd_selfMaskingLaw]
  norm_num

/-- Under `constOutcomeLaw` the response is independent of the outcome (the outcome is constant):
`CondIndepDiscrete` given the trivial covariate. -/
theorem condIndepDiscrete_constOutcomeLaw :
    CondIndepDiscrete constOutcomeLaw {z | z.1 = true} Prod.snd (fun _ => ()) := by
  intro B _ w
  simp only [Set.preimage_const_of_mem (Set.mem_singleton w), Set.inter_univ]
  simp only [constOutcomeLaw, measureReal_half_dirac_add]
  by_cases h1 : (1 : ℝ) ∈ B <;> simp [h1]

/-- Under `selfMaskingLaw` the response is *not* independent of the outcome: given the trivial
covariate, `P(R, Y = 1) = 1/2 ≠ 1/4 = P(R) P(Y = 1)`. -/
theorem not_condIndepDiscrete_selfMaskingLaw :
    ¬ CondIndepDiscrete selfMaskingLaw {z | z.1 = true} Prod.snd (fun _ => ()) := by
  intro h
  have := h {1} (measurableSet_singleton 1) ()
  simp only [Set.preimage_const_of_mem (Set.mem_singleton ()), Set.inter_univ] at this
  simp only [selfMaskingLaw, measureReal_half_dirac_add] at this
  norm_num at this

/-! ### Summary-statistic imputation -/

lemma measurableSet_response : MeasurableSet {z : Bool × ℝ | z.1 = true} :=
  measurable_fst (measurableSet_singleton true)

/-- **Mean imputation estimates the respondents' mean.** Filling every missing outcome with the
respondents' mean `m = E[Y 1_R] / P(R)` gives a completed outcome whose mean is `m` itself. Since
`m` is a functional of the observed-data law, `exists_map_obsRY_eq_integral_ne` shows that it is
the full-data mean only under an assumption on the nonresponse mechanism. -/
theorem integral_ite_respondentMean {P : Measure (Bool × ℝ)} [IsProbabilityMeasure P]
    (hP : Integrable Prod.snd P) (hR : P.real {z | z.1 = true} ≠ 0) :
    ∫ z, (if z.1 then z.2 else
        (∫ w in {w | w.1 = true}, w.2 ∂P) / P.real {w | w.1 = true}) ∂P =
      (∫ w in {w | w.1 = true}, w.2 ∂P) / P.real {w | w.1 = true} := by
  set m := (∫ w in {w | w.1 = true}, w.2 ∂P) / P.real {w | w.1 = true}
  have hsplit : (fun z : Bool × ℝ => if z.1 then z.2 else m) = fun z =>
      {w : Bool × ℝ | w.1 = true}.indicator Prod.snd z +
        {w : Bool × ℝ | w.1 = false}.indicator (fun _ => m) z := by
    funext z
    rcases z with ⟨_ | _, y⟩ <;> simp
  have hcompl : {w : Bool × ℝ | w.1 = false} = {w : Bool × ℝ | w.1 = true}ᶜ := by
    ext z; simp
  rw [hsplit, integral_add (hP.indicator measurableSet_response)
      ((integrable_const m).indicator measurableSet_nonresponse),
    integral_indicator measurableSet_response,
    integral_indicator_const _ measurableSet_nonresponse, hcompl,
    probReal_compl_eq_one_sub measurableSet_response, smul_eq_mul]
  have hm : ∫ w in {w | w.1 = true}, w.2 ∂P = m * P.real {w | w.1 = true} := by
    simp only [m]; rw [div_mul_cancel₀ _ hR]
  rw [hm]
  ring

/-- **Mean imputation is not identification.** Under `selfMaskingLaw` the respondents' mean is
`1`, and so is the mean after mean imputation, while the full-data mean is `1 / 2`. -/
theorem respondentMean_selfMaskingLaw :
    (∫ w in {w | w.1 = true}, w.2 ∂selfMaskingLaw) / selfMaskingLaw.real {w | w.1 = true} = 1 ∧
      ∫ z, z.2 ∂selfMaskingLaw = 1 / 2 := by
  refine ⟨?_, integral_snd_selfMaskingLaw⟩
  rw [← integral_indicator measurableSet_response, selfMaskingLaw, integral_half_dirac_add,
    measureReal_half_dirac_add]
  norm_num

/-! ### Boundary: no respondents -/

/-- With no respondents the observed-data law is the point mass at `(false, 0)`, whatever the
outcome law: the observed data carry no information about `Y`. -/
theorem map_obsRY_eq_dirac_of_measure_response_eq_zero {P : Measure (Bool × ℝ)}
    [IsProbabilityMeasure P] (h : P {z | z.1 = true} = 0) :
    P.map obsRY = Measure.dirac (false, 0) := by
  have hae : (obsRY) =ᵐ[P] fun _ => ((false, 0) : Bool × ℝ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with z hz
    rcases z with ⟨_ | _, y⟩ <;> simp_all
  rw [Measure.map_congr hae, Measure.map_const, measure_univ, one_smul]

/-- With no respondents, any two full-data laws have the same observed-data law. -/
theorem map_obsRY_eq_of_measure_response_eq_zero {P Q : Measure (Bool × ℝ)}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hP : P {z | z.1 = true} = 0)
    (hQ : Q {z | z.1 = true} = 0) : P.map obsRY = Q.map obsRY := by
  rw [map_obsRY_eq_dirac_of_measure_response_eq_zero hP,
    map_obsRY_eq_dirac_of_measure_response_eq_zero hQ]

/-! ### Boundary: positivity failure under MAR -/

section Positivity

variable {𝒳 : Type*} [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]

-- The observed data of a full-data point `(x, r, y)` with an always-observed covariate `x`.
set_option quotPrecheck false in
local notation "obsXRY" => fun z : _ × Bool × ℝ => (z.1, z.2.1, if z.2.1 then z.2.2 else (0 : ℝ))

omit [MeasurableSingletonClass 𝒳] in
lemma measurable_obsXRY : Measurable (obsXRY : 𝒳 × Bool × ℝ → 𝒳 × Bool × ℝ) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk
    (Measurable.ite (p := {z : 𝒳 × Bool × ℝ | z.2.1 = true})
      (measurable_snd.fst (measurableSet_singleton true)) measurable_snd.snd measurable_const))

lemma measurableSet_stratum_nonresponse (x₀ : 𝒳) :
    MeasurableSet {z : 𝒳 × Bool × ℝ | z.1 = x₀ ∧ z.2.1 = false} :=
  (measurable_fst (measurableSet_singleton x₀)).inter
    (measurable_snd.fst (measurableSet_singleton false))

/-- Shift by `c` the outcome of the nonrespondents in the covariate stratum `x = x₀`, leaving
everyone else unchanged. -/
noncomputable def stratumShift (x₀ : 𝒳) (c : ℝ) (z : 𝒳 × Bool × ℝ) : 𝒳 × Bool × ℝ :=
  (z.1, z.2.1, z.2.2 + {z : 𝒳 × Bool × ℝ | z.1 = x₀ ∧ z.2.1 = false}.indicator (fun _ => c) z)

lemma measurable_stratumShift (x₀ : 𝒳) (c : ℝ) : Measurable (stratumShift x₀ c) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.add
    (measurable_const.indicator (measurableSet_stratum_nonresponse x₀))))

omit [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] in
lemma stratumShift_of_ne {x₀ : 𝒳} (c : ℝ) {z : 𝒳 × Bool × ℝ} (h : z.1 ≠ x₀) :
    stratumShift x₀ c z = z := by
  simp [stratumShift, h]

omit [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] in
/-- The stratum shift does not change the observed data. -/
lemma obsXRY_stratumShift (x₀ : 𝒳) (c : ℝ) (z : 𝒳 × Bool × ℝ) :
    (obsXRY) (stratumShift x₀ c z) = (obsXRY) z := by
  rcases z with ⟨x, _ | _, y⟩ <;> simp [stratumShift]

/-- The stratum shift does not change the observed-data law. -/
theorem map_obsXRY_map_stratumShift (P : Measure (𝒳 × Bool × ℝ)) (x₀ : 𝒳) (c : ℝ) :
    (P.map (stratumShift x₀ c)).map obsXRY = P.map obsXRY := by
  rw [Measure.map_map measurable_obsXRY (measurable_stratumShift x₀ c)]
  exact congrArg (fun f => P.map f) (funext (obsXRY_stratumShift x₀ c))

lemma integrable_map_stratumShift {P : Measure (𝒳 × Bool × ℝ)} [IsFiniteMeasure P]
    (hP : Integrable (fun z => z.2.2) P) (x₀ : 𝒳) (c : ℝ) :
    Integrable (fun z => z.2.2) (P.map (stratumShift x₀ c)) :=
  (integrable_map_measure measurable_snd.snd.aestronglyMeasurable
    (measurable_stratumShift x₀ c).aemeasurable).2
    (hP.add ((integrable_const c).indicator (measurableSet_stratum_nonresponse x₀)))

/-- The stratum shift moves the full-data mean by `c P(X = x₀, R = false)`. -/
theorem integral_map_stratumShift {P : Measure (𝒳 × Bool × ℝ)} [IsFiniteMeasure P]
    (hP : Integrable (fun z => z.2.2) P) (x₀ : 𝒳) (c : ℝ) :
    ∫ z, z.2.2 ∂(P.map (stratumShift x₀ c)) =
      ∫ z, z.2.2 ∂P + c * P.real {z | z.1 = x₀ ∧ z.2.1 = false} := by
  rw [integral_map (measurable_stratumShift x₀ c).aemeasurable
    measurable_snd.snd.aestronglyMeasurable]
  simp only [stratumShift]
  rw [integral_add hP ((integrable_const c).indicator (measurableSet_stratum_nonresponse x₀)),
    integral_indicator_const _ (measurableSet_stratum_nonresponse x₀), smul_eq_mul, mul_comm]

/-- If the stratum `x = x₀` has no respondents, the stratum shift preserves the conditional
independence of response and outcome given the covariate (missingness at random). -/
theorem condIndepDiscrete_map_stratumShift {P : Measure (𝒳 × Bool × ℝ)} {x₀ : 𝒳}
    (hMAR : CondIndepDiscrete P {z | z.2.1 = true} (fun z => z.2.2) Prod.fst)
    (hpos : P ({z | z.2.1 = true} ∩ Prod.fst ⁻¹' {x₀}) = 0) (c : ℝ) :
    CondIndepDiscrete (P.map (stratumShift x₀ c)) {z | z.2.1 = true} (fun z => z.2.2)
      Prod.fst := by
  have hS := measurable_stratumShift x₀ c
  have hT : MeasurableSet {z : 𝒳 × Bool × ℝ | z.2.1 = true} :=
    measurable_snd.fst (measurableSet_singleton true)
  intro B hB w
  have hV : MeasurableSet ((fun z : 𝒳 × Bool × ℝ => z.2.2) ⁻¹' B) := measurable_snd.snd hB
  have hW : MeasurableSet (Prod.fst ⁻¹' {w} : Set (𝒳 × Bool × ℝ)) :=
    measurable_fst (measurableSet_singleton w)
  by_cases hw : w = x₀
  · subst hw
    have hTW : stratumShift w c ⁻¹' ({z | z.2.1 = true} ∩ Prod.fst ⁻¹' {w}) =
        {z | z.2.1 = true} ∩ Prod.fst ⁻¹' {w} := by
      ext z; simp [stratumShift]
    have h0 : P.map (stratumShift w c) ({z | z.2.1 = true} ∩ Prod.fst ⁻¹' {w}) = 0 := by
      rw [Measure.map_apply hS (hT.inter hW), hTW, hpos]
    have h0' : P.map (stratumShift w c)
        ({z | z.2.1 = true} ∩ (fun z => z.2.2) ⁻¹' B ∩ Prod.fst ⁻¹' {w}) = 0 :=
      measure_mono_null (Set.inter_subset_inter_left _ Set.inter_subset_left) h0
    simp [Measure.real, h0, h0']
  · -- Off the stratum `x₀` the shift is the identity.
    have hid : ∀ A ⊆ (Prod.fst ⁻¹' {w} : Set (𝒳 × Bool × ℝ)),
        stratumShift x₀ c ⁻¹' A = A := by
      intro A hA
      ext z
      constructor
      · intro hz
        have hz1 : z.1 = w := by
          simpa [stratumShift] using hA hz
        rwa [Set.mem_preimage, stratumShift_of_ne c (hz1 ▸ hw)] at hz
      · intro hz
        have hz1 : z.1 = w := hA hz
        rwa [Set.mem_preimage, stratumShift_of_ne c (hz1 ▸ hw)]
    rw [map_measureReal_apply hS ((hT.inter hV).inter hW),
      map_measureReal_apply hS hW, map_measureReal_apply hS (hT.inter hW),
      map_measureReal_apply hS (hV.inter hW),
      hid _ Set.inter_subset_right, hid _ subset_rfl, hid _ Set.inter_subset_right,
      hid _ Set.inter_subset_right]
    exact hMAR B hB w

/-- **Positivity failure defeats identification even under MAR.** If response is conditionally
independent of the outcome given the covariate, but the stratum `x = x₀` has positive probability
and no respondents, then every real number is the outcome mean of a full-data law that still
satisfies the conditional independence and has the same observed-data law. -/
theorem exists_condIndepDiscrete_map_obsXRY_eq_integral_eq {P : Measure (𝒳 × Bool × ℝ)}
    [IsProbabilityMeasure P] (hP : Integrable (fun z => z.2.2) P)
    (hMAR : CondIndepDiscrete P {z | z.2.1 = true} (fun z => z.2.2) Prod.fst) {x₀ : 𝒳}
    (hpos : P ({z | z.2.1 = true} ∩ Prod.fst ⁻¹' {x₀}) = 0)
    (hx₀ : P.real (Prod.fst ⁻¹' {x₀}) ≠ 0) (t : ℝ) :
    ∃ Q : Measure (𝒳 × Bool × ℝ), IsProbabilityMeasure Q ∧ Integrable (fun z => z.2.2) Q ∧
      CondIndepDiscrete Q {z | z.2.1 = true} (fun z => z.2.2) Prod.fst ∧
      Q.map obsXRY = P.map obsXRY ∧ ∫ z, z.2.2 ∂Q = t := by
  have hstratum : P.real {z : 𝒳 × Bool × ℝ | z.1 = x₀ ∧ z.2.1 = false} =
      P.real (Prod.fst ⁻¹' {x₀}) := by
    refine measureReal_congr (ae_eq_set.2 ⟨?_, ?_⟩)
    · refine measure_mono_null (fun z hz => ?_) (measure_empty (μ := P))
      exact hz.2 hz.1.1
    · refine measure_mono_null (fun z hz => ?_) hpos
      refine ⟨?_, hz.1⟩
      have h1 : z.1 = x₀ := hz.1
      by_contra h2
      exact hz.2 ⟨h1, by simpa using h2⟩
  set c := (t - ∫ z, z.2.2 ∂P) / P.real (Prod.fst ⁻¹' {x₀})
  refine ⟨P.map (stratumShift x₀ c), inferInstance, integrable_map_stratumShift hP x₀ c,
    condIndepDiscrete_map_stratumShift hMAR hpos c, map_obsXRY_map_stratumShift P x₀ c, ?_⟩
  rw [integral_map_stratumShift hP x₀ c, hstratum, div_mul_cancel₀ _ hx₀]
  ring

end Positivity

end MathlibExt.Probability.Causality.MissingData
