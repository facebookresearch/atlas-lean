/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.MissingOutcomes
public import MathlibExt.Probability.Causality.CausalIdentification
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional

/-!
# Missing outcomes: the observed-data map, MCAR and MAR

A unit carries an always-observed covariate `X : Ω → 𝒳`, an outcome `Y : Ω → 𝒴` and a response
event `R : Set Ω` (the respondents); the outcome is recorded only on `R`. As in
`CondIndepDiscrete`, the response indicator is the event itself; Mathlib's independence notions
see it as the `Prop`-valued random variable `ω ↦ ω ∈ R`. This file fixes the vocabulary of
Rubin's missing-data mechanisms. It makes no identification claims.

## Main definitions

* `observedData R X Y`: the observed-data map `ω ↦ (X ω, Y ω or a missing marker)`, valued in
  `𝒳 × (𝒴 ⊕ Unit)` (an `Option 𝒴` encoded as a sum so that it carries Mathlib's measurable
  structure); `Sum.inr ()` is the missing marker.
* `MissingCompletelyAtRandom μ R X Y` (MCAR): `R` is independent of `(X, Y)`, Mathlib's
  `IndepFun`.
* `MissingAtRandomCondIndepFun μ R X hX Y` (MAR): `R` is conditionally independent of `Y` given
  `σ(X)`, Mathlib's `CondIndepFun` (which needs a standard Borel sample space and a finite
  measure). It is named apart from the discrete-covariate predicate
  `MathlibExt.Probability.Causality.MissingOutcomes.MissingAtRandom μ R Y X`.

## Main results

* `observedData_congr`: the observed data do not depend on the outcome of nonrespondents.
* `measurable_observedData`: the observed-data map is measurable, so its law `μ.map` exists.
* `missingCompletelyAtRandom_iff`: for a probability measure, MCAR holds iff the response event
  factorizes against every event of `(X, Y)`; `missingCompletelyAtRandom_iff_condIndepDiscrete`
  restates this as `CondIndepDiscrete μ R (fun ω => (X ω, Y ω)) (fun _ => ())`.
* `condExp_indicator_comap_ae_eq`: for a countably valued `X`, `P(E | σ(X)) = propensity μ E X X`
  almost everywhere.
* `missingAtRandomCondIndepFun_iff_condIndepDiscrete`: on the common domain (a countably valued
  `X` with measurable singletons), MAR is exactly `CondIndepDiscrete μ R Y X` from
  `MathlibExt.Probability.Causality.CausalIdentification`.
* `missingAtRandomCondIndepFun_iff_missingAtRandom`: for a real outcome on that domain, the two
  named MAR predicates agree: `MissingAtRandomCondIndepFun μ R X hX Y` holds iff
  `MissingOutcomes.MissingAtRandom μ R Y X` does.
* `MissingCompletelyAtRandom.condIndepDiscrete`,
  `MissingCompletelyAtRandom.missingAtRandomCondIndepFun`: MCAR implies MAR.

## Not covered

Missing-not-at-random mechanisms, identification of the outcome mean (complete-case and
inverse-response weighting) and nonidentification counterexamples; covariates that are themselves
missing; monotone or longitudinal missingness patterns.

`MissingAtRandomCondIndepFun` assumes a standard Borel sample space (inherited from Mathlib's
`CondIndepFun`) and is not bridged to the general conditional-expectation form
`μ[R.indicator Y | m] =ᵐ μ[R.indicator 1 | m] * μ[Y | m]` for an arbitrary sub-σ-algebra `m`,
the hypothesis of the general inverse-weighting theorem `integral_ipw_treated_condExp`.

## References

* D. B. Rubin, *Inference and missing data*, Biometrika 63(3) (1976), 581–592 (the MCAR / MAR
  hierarchy, Section 3).
* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley
  (2019), Section 1.3 (missingness mechanisms with fully observed covariates).
-/

@[expose] public section

namespace MathlibExt.Probability.Causality.MissingData

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Causality (propensity CondIndepDiscrete)

variable {Ω 𝒳 𝒴 : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### The observed-data map -/

open Classical in
/-- The observed-data map: the covariate `X ω` together with `Sum.inl (Y ω)` for a respondent
`ω ∈ R` and the missing marker `Sum.inr ()` for a nonrespondent. The second component is an
`Option 𝒴` written as `𝒴 ⊕ Unit`, which carries Mathlib's measurable structure. -/
noncomputable def observedData (R : Set Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) : Ω → 𝒳 × (𝒴 ⊕ Unit) :=
  fun ω => (X ω, if ω ∈ R then Sum.inl (Y ω) else Sum.inr ())

@[simp]
theorem observedData_fst (R : Set Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) (ω : Ω) :
    (observedData R X Y ω).1 = X ω :=
  rfl

theorem observedData_of_mem {R : Set Ω} (X : Ω → 𝒳) (Y : Ω → 𝒴) {ω : Ω} (h : ω ∈ R) :
    observedData R X Y ω = (X ω, Sum.inl (Y ω)) := by
  simp [observedData, h]

theorem observedData_of_notMem {R : Set Ω} (X : Ω → 𝒳) (Y : Ω → 𝒴) {ω : Ω} (h : ω ∉ R) :
    observedData R X Y ω = (X ω, Sum.inr ()) := by
  simp [observedData, h]

/-- The observed data reveal the response indicator. -/
@[simp]
theorem observedData_snd_isLeft (R : Set Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) (ω : Ω) :
    (observedData R X Y ω).2.isLeft = true ↔ ω ∈ R := by
  by_cases h : ω ∈ R <;> simp [observedData, h]

/-- The observed data do not depend on the outcome of nonrespondents: two outcomes that agree on
the respondents give the same observed-data map. -/
theorem observedData_congr {R : Set Ω} (X : Ω → 𝒳) {Y Y' : Ω → 𝒴}
    (h : ∀ ω ∈ R, Y ω = Y' ω) : observedData R X Y = observedData R X Y' := by
  funext ω
  by_cases hω : ω ∈ R
  · simp [observedData, hω, h ω hω]
  · simp [observedData, hω]

variable [m𝒳 : MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

theorem measurable_observedData {R : Set Ω} {X : Ω → 𝒳} {Y : Ω → 𝒴} (hR : MeasurableSet R)
    (hX : Measurable X) (hY : Measurable Y) : Measurable (observedData R X Y) :=
  hX.prodMk (Measurable.ite hR (measurable_inl.comp hY) measurable_const)

/-! ### Missingness mechanisms -/

/-- **Missing completely at random** (Rubin 1976): the response indicator `ω ↦ ω ∈ R` (a
`Prop`-valued random variable) is independent of the full data `(X, Y)`. -/
def MissingCompletelyAtRandom (μ : Measure Ω) (R : Set Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) : Prop :=
  IndepFun (· ∈ R) (fun ω => (X ω, Y ω)) μ

/-- **Missing at random** (Rubin 1976): the response indicator `ω ↦ ω ∈ R` is conditionally
independent of the outcome `Y` given the always-observed covariate `X`, as Mathlib's
`CondIndepFun` given the σ-algebra `σ(X)`. The measurability proof `hX` only certifies
`σ(X) ≤ mΩ`. The discrete-covariate form used by the AIPW development is
`MathlibExt.Probability.Causality.MissingOutcomes.MissingAtRandom`; the two agree on their
common domain (`missingAtRandomCondIndepFun_iff_missingAtRandom`). -/
def MissingAtRandomCondIndepFun [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Set Ω) (X : Ω → 𝒳) (hX : Measurable X) (Y : Ω → 𝒴) : Prop :=
  CondIndepFun (m𝒳.comap X) hX.comap_le (· ∈ R) Y μ

/-! ### MCAR through the response event -/

omit [MeasurableSpace 𝒴] in
private lemma measurable_mem_set {R : Set Ω} (hR : MeasurableSet R) :
    Measurable (· ∈ R : Ω → Prop) :=
  measurableSet_setOfPred.1 hR

omit [MeasurableSpace 𝒴] in
private lemma preimage_mem_true (R : Set Ω) : (· ∈ R) ⁻¹' {True} = R := by
  ext ω; simp

omit [MeasurableSpace 𝒴] in
/-- A set of propositions pulls back under `ω ↦ ω ∈ R` to `∅`, `R`, `Rᶜ` or everything. -/
private lemma preimage_mem_cases (R : Set Ω) (s : Set Prop) :
    (· ∈ R) ⁻¹' s = ∅ ∨ (· ∈ R) ⁻¹' s = R ∨ (· ∈ R) ⁻¹' s = Rᶜ ∨
      (· ∈ R) ⁻¹' s = Set.univ := by
  by_cases h1 : True ∈ s <;> by_cases h2 : False ∈ s
  · refine Or.inr (Or.inr (Or.inr ?_))
    ext ω; by_cases h : ω ∈ R <;> simp [h, h1, h2]
  · refine Or.inr (Or.inl ?_)
    ext ω; by_cases h : ω ∈ R <;> simp [h, h1, h2]
  · refine Or.inr (Or.inr (Or.inl ?_))
    ext ω; by_cases h : ω ∈ R <;> simp [h, h1, h2]
  · refine Or.inl ?_
    ext ω; by_cases h : ω ∈ R <;> simp [h, h1, h2]

omit [MeasurableSpace 𝒴] in
private lemma measureReal_compl_inter [IsFiniteMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    (C : Set Ω) : μ.real (Tᶜ ∩ C) = μ.real C - μ.real (T ∩ C) := by
  have h := measureReal_inter_add_sdiff (μ := μ) (s := C) hT
  rw [Set.sdiff_eq, Set.inter_comm C Tᶜ, Set.inter_comm C T] at h
  linarith

/-- Under MCAR the response event factorizes against every event of the full data. -/
private lemma MissingCompletelyAtRandom.measureReal_inter {R : Set Ω} {X : Ω → 𝒳} {Y : Ω → 𝒴}
    (h : MissingCompletelyAtRandom μ R X Y) {t : Set (𝒳 × 𝒴)} (ht : MeasurableSet t) :
    μ.real (R ∩ (fun ω => (X ω, Y ω)) ⁻¹' t) =
      μ.real R * μ.real ((fun ω => (X ω, Y ω)) ⁻¹' t) := by
  have key := (indepFun_iff_measure_inter_preimage_eq_mul.1 h) {True} t
    (measurableSet_singleton _) ht
  rw [preimage_mem_true] at key
  simp only [measureReal_def, key, ENNReal.toReal_mul]

/-- For a probability measure, MCAR holds iff the response event factorizes against every event
of the full data `(X, Y)`. -/
theorem missingCompletelyAtRandom_iff [IsProbabilityMeasure μ] {R : Set Ω} {X : Ω → 𝒳}
    {Y : Ω → 𝒴} (hR : MeasurableSet R) :
    MissingCompletelyAtRandom μ R X Y ↔
      ∀ t, MeasurableSet t → μ.real (R ∩ (fun ω => (X ω, Y ω)) ⁻¹' t) =
        μ.real R * μ.real ((fun ω => (X ω, Y ω)) ⁻¹' t) := by
  refine ⟨fun h t ht => h.measureReal_inter ht, fun h => ?_⟩
  rw [MissingCompletelyAtRandom, indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ ht
  set Z := fun ω => (X ω, Y ω)
  suffices hreal : μ.real ((· ∈ R) ⁻¹' s ∩ Z ⁻¹' t) = μ.real ((· ∈ R) ⁻¹' s) * μ.real (Z ⁻¹' t) by
    rw [← ofReal_measureReal, ← ofReal_measureReal, ← ofReal_measureReal,
      ← ENNReal.ofReal_mul measureReal_nonneg, hreal]
  rcases preimage_mem_cases R s with hs | hs | hs | hs <;> rw [hs]
  · simp
  · exact h t ht
  · rw [measureReal_compl_inter hR, measureReal_compl hR, h t ht, probReal_univ]
    ring
  · simp

/-- **MCAR as a discrete conditional independence.** For a probability measure, MCAR is
`CondIndepDiscrete` of the response event and the full data given a constant. -/
theorem missingCompletelyAtRandom_iff_condIndepDiscrete [IsProbabilityMeasure μ] {R : Set Ω}
    {X : Ω → 𝒳} {Y : Ω → 𝒴} (hR : MeasurableSet R) :
    MissingCompletelyAtRandom μ R X Y ↔
      CondIndepDiscrete μ R (fun ω => (X ω, Y ω)) (fun _ => ()) := by
  have hc : ∀ w : Unit, (fun _ : Ω => ()) ⁻¹' {w} = Set.univ :=
    fun w => Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  rw [missingCompletelyAtRandom_iff hR]
  refine ⟨fun h B hB w => ?_, fun h t ht => ?_⟩
  · rw [hc, Set.inter_univ, Set.inter_univ, Set.inter_univ, probReal_univ, mul_one]
    exact h B hB
  · have key := h t ht ()
    rwa [hc, Set.inter_univ, Set.inter_univ, Set.inter_univ, probReal_univ, mul_one] at key

/-- MCAR implies the discrete conditional independence `R ⊥ Y | X` of the response event. -/
theorem MissingCompletelyAtRandom.condIndepDiscrete [MeasurableSingletonClass 𝒳] {R : Set Ω}
    {X : Ω → 𝒳} {Y : Ω → 𝒴} (h : MissingCompletelyAtRandom μ R X Y) :
    CondIndepDiscrete μ R Y X := by
  intro B hB x
  have hYX : Y ⁻¹' B ∩ X ⁻¹' {x} = (fun ω => (X ω, Y ω)) ⁻¹' ({x} ×ˢ B) := by
    ext ω; simp [and_comm]
  have hX : X ⁻¹' {x} = (fun ω => (X ω, Y ω)) ⁻¹' ({x} ×ˢ Set.univ) := by
    ext ω; simp
  rw [Set.inter_assoc, hYX, h.measureReal_inter ((measurableSet_singleton x).prod hB), hX,
    h.measureReal_inter ((measurableSet_singleton x).prod MeasurableSet.univ)]
  ring

/-! ### Conditional probabilities given a countably valued covariate -/

omit m𝒳 in
private lemma propensity_nonneg (E : Set Ω) (X : Ω → 𝒳) (x : 𝒳) : 0 ≤ propensity μ E X x :=
  div_nonneg measureReal_nonneg measureReal_nonneg

omit m𝒳 in
private lemma propensity_le_one [IsFiniteMeasure μ] (E : Set Ω) (X : Ω → 𝒳) (x : 𝒳) :
    propensity μ E X x ≤ 1 :=
  div_le_one_of_le₀ (measureReal_mono Set.inter_subset_right) measureReal_nonneg

omit m𝒳 in
private lemma measureReal_mul_propensity [IsFiniteMeasure μ] (E : Set Ω) (X : Ω → 𝒳) (x : 𝒳) :
    μ.real (X ⁻¹' {x}) * propensity μ E X x = μ.real (E ∩ X ⁻¹' {x}) := by
  by_cases h : μ.real (X ⁻¹' {x}) = 0
  · rw [h, zero_mul]
    exact (measureReal_mono_null Set.inter_subset_right h).symm
  · rw [propensity, mul_div_cancel₀ _ h]

/-- For a countably valued covariate `X`, the conditional probability of an event `E` given
`σ(X)` is the propensity `P(E ∩ {X = x}) / P(X = x)` evaluated at `x = X ω`, almost everywhere. -/
theorem condExp_indicator_comap_ae_eq [IsFiniteMeasure μ] [Countable 𝒳]
    [MeasurableSingletonClass 𝒳] {X : Ω → 𝒳} (hX : Measurable X) {E : Set Ω}
    (hE : MeasurableSet E) :
    μ⟦E | m𝒳.comap X⟧ =ᵐ[μ] fun ω => propensity μ E X (X ω) := by
  have hm := hX.comap_le
  have hgm : Measurable[m𝒳.comap X] fun ω => propensity μ E X (X ω) :=
    (measurable_of_countable fun x => propensity μ E X x).comp (comap_measurable X)
  have hgi : Integrable (fun ω => propensity μ E X (X ω)) μ :=
    Integrable.of_bound (hgm.mono hm le_rfl).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (propensity_nonneg E X _)]
        exact propensity_le_one E X _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm ((integrable_const (1 : ℝ)).indicator hE)
    (fun _ _ _ => hgi.integrableOn) (fun s hs _ => ?_) hgm.aestronglyMeasurable).symm
  obtain ⟨A, -, rfl⟩ := hs
  have hU : X ⁻¹' A = ⋃ x, X ⁻¹' A ∩ X ⁻¹' {x} := by
    ext ω; simp
  have hmeas : ∀ x, MeasurableSet (X ⁻¹' A ∩ X ⁻¹' {x}) := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.inter_eq_right.2 (Set.preimage_mono (Set.singleton_subset_iff.2 hx))]
      exact hX (measurableSet_singleton x)
    · rw [← Set.preimage_inter, Set.inter_singleton_eq_empty.2 hx, Set.preimage_empty]
      exact MeasurableSet.empty
  have hdisj : Pairwise (Function.onFun Disjoint fun x => X ⁻¹' A ∩ X ⁻¹' {x}) :=
    fun x y hxy => Set.disjoint_left.2 fun ω h1 h2 => hxy (h1.2.symm.trans h2.2)
  rw [hU, integral_iUnion hmeas hdisj hgi.integrableOn,
    integral_iUnion hmeas hdisj ((integrable_const (1 : ℝ)).indicator hE).integrableOn]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ A
  · rw [Set.inter_eq_right.2 (Set.preimage_mono (Set.singleton_subset_iff.2 hx))]
    have hSx : MeasurableSet (X ⁻¹' {x}) := hX (measurableSet_singleton x)
    rw [setIntegral_congr_fun hSx (g := fun _ => propensity μ E X x) fun ω hω => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
        simp only [hω],
      setIntegral_const, smul_eq_mul, measureReal_mul_propensity,
      integral_indicator hE, setIntegral_const, measureReal_restrict_apply hE, smul_eq_mul,
      mul_one]
  · rw [← Set.preimage_inter, Set.inter_singleton_eq_empty.2 hx, Set.preimage_empty]
    simp

/-! ### MAR on the common domain: the bridge to `CondIndepDiscrete` -/

omit m𝒳 in
/-- Two functions of a countably valued `X` agree almost everywhere iff they agree at every value
of positive probability. -/
private lemma ae_comp_eq_iff [Countable 𝒳] {X : Ω → 𝒳} {f g : 𝒳 → ℝ} :
    (fun ω => f (X ω)) =ᵐ[μ] (fun ω => g (X ω)) ↔ ∀ x, μ (X ⁻¹' {x}) ≠ 0 → f x = g x := by
  constructor
  · intro h x hx
    by_contra hne
    refine hx (measure_mono_null (fun ω hω => ?_) (ae_iff.1 h))
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp [hω, hne]
  · intro h
    have hsub : {ω | ¬f (X ω) = g (X ω)} ⊆ ⋃ x, {ω | X ω = x ∧ f x ≠ g x} :=
      fun ω hω => Set.mem_iUnion.2 ⟨X ω, rfl, hω⟩
    refine ae_iff.2 (measure_mono_null hsub (measure_iUnion_null fun x => ?_))
    by_cases hfg : f x = g x
    · simp [hfg]
    · exact measure_mono_null (fun ω hω => hω.1) (not_imp_comm.1 (h x) hfg)

omit m𝒳 in
/-- At a value `x` of positive probability, the product rule for propensities is the
cross-multiplied product rule for the joint probabilities with `{X = x}`. -/
private lemma propensity_inter_eq_mul_iff {A B : Set Ω} {X : Ω → 𝒳} {x : 𝒳}
    (hx : μ.real (X ⁻¹' {x}) ≠ 0) :
    propensity μ (A ∩ B) X x = propensity μ A X x * propensity μ B X x ↔
      μ.real (A ∩ B ∩ X ⁻¹' {x}) * μ.real (X ⁻¹' {x}) =
        μ.real (A ∩ X ⁻¹' {x}) * μ.real (B ∩ X ⁻¹' {x}) := by
  rw [propensity, propensity, propensity, div_mul_div_comm,
    div_eq_div_iff hx (mul_ne_zero hx hx), ← mul_assoc, mul_left_inj' hx]

/-- **MAR on the common domain.** For a countably valued covariate `X` with measurable singletons,
missing at random (Mathlib's conditional independence `R ⊥ Y | σ(X)`) is exactly the discrete
conditional independence `CondIndepDiscrete μ R Y X` of the response event. -/
theorem missingAtRandomCondIndepFun_iff_condIndepDiscrete [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    [Countable 𝒳] [MeasurableSingletonClass 𝒳] {R : Set Ω} {X : Ω → 𝒳} {Y : Ω → 𝒴}
    (hR : MeasurableSet R) (hX : Measurable X) (hY : Measurable Y) :
    MissingAtRandomCondIndepFun μ R X hX Y ↔ CondIndepDiscrete μ R Y X := by
  have hR' := measurable_mem_set hR
  rw [MissingAtRandomCondIndepFun, condIndepFun_iff_condExp_inter_preimage_eq_mul hR' hY]
  have key : ∀ s t, MeasurableSet s → MeasurableSet t →
      (((μ⟦(· ∈ R) ⁻¹' s ∩ Y ⁻¹' t | m𝒳.comap X⟧) =ᵐ[μ]
          fun ω => (μ⟦(· ∈ R) ⁻¹' s | m𝒳.comap X⟧) ω * (μ⟦Y ⁻¹' t | m𝒳.comap X⟧) ω) ↔
        ∀ x, μ.real (X ⁻¹' {x}) ≠ 0 →
          μ.real ((· ∈ R) ⁻¹' s ∩ Y ⁻¹' t ∩ X ⁻¹' {x}) * μ.real (X ⁻¹' {x}) =
            μ.real ((· ∈ R) ⁻¹' s ∩ X ⁻¹' {x}) * μ.real (Y ⁻¹' t ∩ X ⁻¹' {x})) := by
    intro s t hs ht
    have h1 := condExp_indicator_comap_ae_eq (μ := μ) hX ((hR' hs).inter (hY ht))
    have h2 := (condExp_indicator_comap_ae_eq (μ := μ) hX (hR' hs)).mul
      (condExp_indicator_comap_ae_eq (μ := μ) hX (hY ht))
    have hiff : ((μ⟦(· ∈ R) ⁻¹' s ∩ Y ⁻¹' t | m𝒳.comap X⟧) =ᵐ[μ]
          fun ω => (μ⟦(· ∈ R) ⁻¹' s | m𝒳.comap X⟧) ω * (μ⟦Y ⁻¹' t | m𝒳.comap X⟧) ω) ↔
        (fun ω => propensity μ ((· ∈ R) ⁻¹' s ∩ Y ⁻¹' t) X (X ω)) =ᵐ[μ]
          fun ω => propensity μ ((· ∈ R) ⁻¹' s) X (X ω) * propensity μ (Y ⁻¹' t) X (X ω) :=
      ⟨fun h => h1.symm.trans (h.trans h2), fun h => h1.trans (h.trans h2.symm)⟩
    rw [hiff, ae_comp_eq_iff (f := fun x => propensity μ ((· ∈ R) ⁻¹' s ∩ Y ⁻¹' t) X x)
      (g := fun x => propensity μ ((· ∈ R) ⁻¹' s) X x * propensity μ (Y ⁻¹' t) X x)]
    refine forall_congr' fun x => ?_
    have hne : μ.real (X ⁻¹' {x}) ≠ 0 ↔ μ (X ⁻¹' {x}) ≠ 0 := (measureReal_eq_zero_iff).not
    rw [← hne]
    exact imp_congr_right fun hx => propensity_inter_eq_mul_iff hx
  constructor
  · intro H B hB x
    by_cases hx : μ.real (X ⁻¹' {x}) = 0
    · rw [hx, mul_zero, measureReal_mono_null (Set.inter_subset_right (s := R)) hx, zero_mul]
    · have hk := (key {True} B (measurableSet_singleton _) hB).1
        (H {True} B (measurableSet_singleton _) hB) x hx
      rwa [preimage_mem_true] at hk
  · intro hCI s t hs ht
    refine (key s t hs ht).2 fun x _ => ?_
    rcases preimage_mem_cases R s with h | h | h | h <;> rw [h]
    · simp
    · exact hCI t ht x
    · have hc := hCI t ht x
      rw [Set.inter_assoc, measureReal_compl_inter hR, measureReal_compl_inter hR]
      rw [Set.inter_assoc] at hc
      linear_combination (-1 : ℝ) * hc
    · simp only [Set.univ_inter]
      ring

/-- **The two named MAR predicates agree.** For a real outcome and a countably valued covariate
with measurable singletons, `MissingAtRandomCondIndepFun` (Mathlib's `CondIndepFun` given `σ(X)`)
holds iff the discrete-covariate predicate `MissingOutcomes.MissingAtRandom` of the AIPW
development does. Note the argument orders: `R X hX Y` here, `R Y X` there. -/
theorem missingAtRandomCondIndepFun_iff_missingAtRandom [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] [Countable 𝒳] [MeasurableSingletonClass 𝒳] {R : Set Ω} {X : Ω → 𝒳}
    {Y : Ω → ℝ} (hR : MeasurableSet R) (hX : Measurable X) (hY : Measurable Y) :
    MissingAtRandomCondIndepFun μ R X hX Y ↔ MissingOutcomes.MissingAtRandom μ R Y X :=
  missingAtRandomCondIndepFun_iff_condIndepDiscrete hR hX hY

/-- MCAR implies MAR, for a countably valued covariate. -/
theorem MissingCompletelyAtRandom.missingAtRandomCondIndepFun [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] [Countable 𝒳] [MeasurableSingletonClass 𝒳] {R : Set Ω} {X : Ω → 𝒳}
    {Y : Ω → 𝒴} (h : MissingCompletelyAtRandom μ R X Y) (hR : MeasurableSet R)
    (hX : Measurable X) (hY : Measurable Y) : MissingAtRandomCondIndepFun μ R X hX Y :=
  (missingAtRandomCondIndepFun_iff_condIndepDiscrete hR hX hY).2 h.condIndepDiscrete

end MathlibExt.Probability.Causality.MissingData
