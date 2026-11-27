/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.MNARCounterexample

/-!
# Sharp no-assumption bounds for a mean with missing outcomes

With a known outcome range, fixing the law of the response bit and the observed outcome fixes
both the response rate and the contribution of respondents to the mean. The remaining
contribution can be any point from the lower to the upper outcome bound times the nonresponse
probability, without any missingness or positivity assumption.

## References

* Charles F. Manski, *Partial Identification of Probability Distributions*, Springer, 2003,
  §1.2 “Means”, Proposition 1.1, <https://doi.org/10.1007/0-387-21786-X_2>.
* Charles F. Manski, “Anatomy of the Selection Problem”, *Journal of Human Resources* 24(3),
  1989, pp. 343–360, <https://doi.org/10.2307/145818>, for the earlier support-bound approach
  to mean regression under selective observation.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality.MissingData

open MeasureTheory ProbabilityTheory

set_option quotPrecheck false in
local notation "obsRY" => fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))

set_option quotPrecheck false in
local notation "respondents" => {z : Bool × ℝ | z.1 = true}
set_option quotPrecheck false in
local notation "nonrespondents" => {z : Bool × ℝ | z.1 = false}

private theorem response_compl : (respondents : Set (Bool × ℝ))ᶜ = nonrespondents := by
  ext ⟨r, y⟩
  cases r <;> simp

private theorem observed_contribution (P : Measure (Bool × ℝ)) :
    (∫ z, z.2 ∂(P.map obsRY)) = ∫ z in respondents, z.2 ∂P := by
  rw [integral_map measurable_obsRY.aemeasurable measurable_snd.aestronglyMeasurable,
    ← integral_indicator measurableSet_response]
  congr 1
  funext z
  rcases z with ⟨r, y⟩
  cases r <;> simp

private theorem nonresponse_mass (P : Measure (Bool × ℝ)) [IsProbabilityMeasure P] :
    P.real nonrespondents = 1 - P.real respondents := by
  rw [← response_compl, measureReal_compl measurableSet_response, probReal_univ]

private theorem response_mass_eq {P Q : Measure (Bool × ℝ)}
    (h : Q.map obsRY = P.map obsRY) : Q.real respondents = P.real respondents := by
  have hpre : obsRY ⁻¹' (respondents : Set (Bool × ℝ)) = respondents := rfl
  have hm := congrArg (fun M : Measure (Bool × ℝ) => M respondents) h
  rw [Measure.map_apply measurable_obsRY measurableSet_response,
    Measure.map_apply measurable_obsRY measurableSet_response, hpre] at hm
  exact congrArg ENNReal.toReal hm

private noncomputable def fillNonresponse (t : ℝ) : Bool × ℝ → Bool × ℝ :=
  fun z => (z.1, if z.1 then z.2 else t)

private theorem measurable_fillNonresponse (t : ℝ) : Measurable (fillNonresponse t) :=
  measurable_fst.prodMk (Measurable.ite measurableSet_response measurable_snd measurable_const)

private theorem map_obsRY_fillNonresponse (P : Measure (Bool × ℝ)) (t : ℝ) :
    (P.map (fillNonresponse t)).map obsRY = P.map obsRY := by
  rw [Measure.map_map measurable_obsRY (measurable_fillNonresponse t)]
  congr 1
  funext z
  rcases z with ⟨r, y⟩
  cases r <;> rfl

private theorem snd_integral_fillNonresponse {P : Measure (Bool × ℝ)} [IsFiniteMeasure P]
    (hP : Integrable Prod.snd P) (t : ℝ) :
    (∫ z, z.2 ∂(P.map (fillNonresponse t))) =
      (∫ z, z.2 ∂(P.map obsRY)) + P.real nonrespondents * t := by
  have hfill (z : Bool × ℝ) : (fillNonresponse t z).2 =
      (respondents : Set (Bool × ℝ)).indicator Prod.snd z +
        (nonrespondents : Set (Bool × ℝ)).indicator (fun _ => t) z := by
    rcases z with ⟨r, y⟩
    cases r <;> simp [fillNonresponse]
  rw [integral_map (measurable_fillNonresponse t).aemeasurable
    measurable_snd.aestronglyMeasurable, observed_contribution]
  simp only [hfill]
  rw [integral_add (hP.indicator measurableSet_response)
    ((integrable_const t).indicator measurableSet_nonresponse),
    integral_indicator measurableSet_response, integral_indicator_const _ measurableSet_nonresponse,
    smul_eq_mul]

/-- **Worst-case bounds for a mean with missing outcomes.** Let `P` be a probability law of a
response bit `R` and a real outcome `Y` known to lie in `[a, b]`. Let `q = P(R = true)` and
`A = E[R Y]`, where missing outcomes are recorded as zero. Among all probability laws with the
same observed-data law of `(R, R Y)` and outcome range `[a, b]`, the possible full-data means
form exactly `[A + (1 - q) a, A + (1 - q) b]`. Every point can be attained by assigning a single
constant in `[a, b]` to the missing outcomes. The interval includes full and zero response:
when `q = 1` it reduces to `A`, and when `q = 0` it is `[a, b]`.

This is the bounded identity-function case of Manski (2003), Proposition 1.1,
written without conditioning on the response bit. -/
theorem missingOutcomeMean_identifiedSet_eq_Icc (P : Measure (Bool × ℝ))
    [IsProbabilityMeasure P] {a b : ℝ} (hP : ∀ᵐ z ∂P, z.2 ∈ Set.Icc a b) :
    let q := P.real respondents
    let A := ∫ z, z.2 ∂(P.map obsRY)
    {m : ℝ | ∃ Q : Measure (Bool × ℝ), IsProbabilityMeasure Q ∧
        (∀ᵐ z ∂Q, z.2 ∈ Set.Icc a b) ∧ Q.map obsRY = P.map obsRY ∧
        (∫ z, z.2 ∂Q) = m} = Set.Icc (A + (1 - q) * a) (A + (1 - q) * b) := by
  intro q A
  have hp := Integrable.of_mem_Icc a b measurable_snd.aemeasurable hP
  have hmass : P.real nonrespondents = 1 - q := nonresponse_mass P
  have hq : 0 ≤ 1 - q := by rw [← hmass]; exact measureReal_nonneg
  ext m
  constructor
  · rintro ⟨Q, hprob, hQ, hobs, rfl⟩
    let : IsProbabilityMeasure Q := hprob
    have hi := Integrable.of_mem_Icc a b measurable_snd.aemeasurable hQ
    have hqm : Q.real nonrespondents = 1 - q := by
      rw [nonresponse_mass Q, response_mass_eq hobs]
    have hresp : (∫ z in respondents, z.2 ∂Q) = A := by
      rw [← observed_contribution Q, hobs]
    have hrange : ∀ᵐ z ∂Q.restrict nonrespondents, z.2 ∈ Set.Icc a b := ae_restrict_le hQ
    have hlower := integral_mono_ae (integrable_const a) hi.integrableOn
      (hrange.mono fun _ hz => hz.1)
    have hupper := integral_mono_ae hi.integrableOn (integrable_const b)
      (hrange.mono fun _ hz => hz.2)
    rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul, hqm]
      at hlower hupper
    rw [← integral_add_compl measurableSet_response hi, response_compl, hresp]
    exact ⟨add_le_add le_rfl hlower, add_le_add le_rfl hupper⟩
  · intro hm
    change A + (1 - q) * a ≤ m ∧ m ≤ A + (1 - q) * b at hm
    have hw : ∃ t ∈ Set.Icc a b, A + (1 - q) * t = m := by
      rcases hq.eq_or_lt with hz | hpos
      · obtain ⟨_, hz'⟩ := hP.exists
        have hab : a ≤ b := hz'.1.trans hz'.2
        simp only [← hz, zero_mul, add_zero] at hm
        exact ⟨a, ⟨le_rfl, hab⟩, by simpa only [← hz, zero_mul, add_zero] using
          (le_antisymm hm.1 hm.2 : A = m)⟩
      · refine ⟨(m - A) / (1 - q), ⟨(le_div_iff₀ hpos).2 ?_, (div_le_iff₀ hpos).2 ?_⟩, ?_⟩
        · linarith [hm.1]
        · linarith [hm.2]
        · rw [mul_comm (1 - q), div_mul_cancel₀ _ hpos.ne']
          ring
    obtain ⟨t, ht, htmean⟩ := hw
    have htmeas := measurable_fillNonresponse t
    refine ⟨P.map (fillNonresponse t), inferInstance,
      (ae_map_iff htmeas.aemeasurable (measurable_snd measurableSet_Icc)).2 ?_,
      map_obsRY_fillNonresponse P t, ?_⟩
    · filter_upwards [hP] with z hz
      rcases z with ⟨r, y⟩
      cases r
      · simpa [fillNonresponse] using ht
      · simpa [fillNonresponse] using hz
    · rw [snd_integral_fillNonresponse hp, hmass]
      exact htmean

end MathlibExt.Probability.Causality.MissingData
