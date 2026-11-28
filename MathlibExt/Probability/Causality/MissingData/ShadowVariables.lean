/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.Definitions
public import MathlibExt.Probability.WeightLaw

/-!
# Missing not at random: identification with a shadow variable

An outcome `Y` is missing for nonrespondents (`R = false`), and a *shadow variable* `Z` is always
observed. The full data are `(R, Y, Z)`; the observed data are `(R, Y, Z)` on response and
`(R, Z)` on nonresponse. Response may depend on the missing outcome itself (missing not at
random), so without further assumptions the full-data law is not identified
(`MNARCounterexample`). A shadow variable restores identification (Miao and Tchetgen Tchetgen;
Wang, Shao and Kim) under two assumptions:

* **shadow**: `Z` is conditionally independent of the response given the outcome, `Z ⊥ R | Y`;
* **completeness**: the law of `Y` given `Z` among respondents is complete, i.e. for every `g`,
  `E[g(Y) | Z, R = true] = 0` forces `g = 0`.

Here `Y` and `Z` take finitely many values, so completeness is the injectivity of the matrix
`(P(R = true, Y = y, Z = z))_{z, y}`.

Under the shadow assumption, `P(R = false, Y = y, Z = z) = a(y) P(R = true, Y = y, Z = z)` with
the nonresponse odds `a(y) = P(R = false, Y = y) / P(R = true, Y = y)`. Summing over `y` gives the
integral equation `∑ y, a(y) P(R = true, Y = y, Z = z) = P(R = false, Z = z)`, whose coefficients
are observed; completeness makes its solution unique. The odds, hence the full-data law, are then
determined by the observed-data law.

## Main definitions

* `shadowObs`: the observed data of a full-data point, the canonical map `observedData R X Y`
  with `R = {r = true}`, `X = z` and `Y = y`: `(z, Sum.inl y)` on response and
  `(z, Sum.inr ())` on nonresponse.
* `ShadowVariable P`: `Z ⊥ R | Y` under `P`, as `CondIndepDiscrete`.
* `ShadowComplete P`: completeness of the respondents' outcome given the shadow variable.
* `shadowOdds P y`: the nonresponse odds `P(R = false, Y = y) / P(R = true, Y = y)`.

## Main results

* `map_shadowObs_eq_iff`: two full-data laws have the same observed-data law exactly when they
  agree on the respondent cells `(true, y, z)` and on the nonrespondent shadow margins.
* `ShadowVariable.measureReal_false_eq`: the shadow factorization of the nonrespondent cells, and
  `shadowVariable_of_odds`, its converse.
* `ShadowComplete.sum_ne_zero`: completeness forces every outcome value to have respondents.
* `ShadowVariable.sum_shadowOdds_mul`, `ShadowComplete.eq_shadowOdds`: the odds solve the observed
  integral equation, and under completeness they are its only solution.
* `eq_of_map_shadowObs_eq` (**identification**): two shadow laws with the same observed-data law,
  one of them complete, are equal. `integral_eq_of_map_shadowObs_eq`: in particular every
  outcome mean is identified.
* `exists_ne_map_shadowObs_eq_of_not_shadowComplete` (**completeness is necessary**): at a shadow
  law with `0 < P(R = true | Y = y) < 1` for every `y` that is not complete, a different shadow
  law has the same observed-data law.

## Implementation notes

A covariate `X` that is always observed is handled stratum by stratum: condition every statement
on `X = x`. The proofs reduce every event to point masses (`measureReal_eq_sum`), so they use
only the finiteness of `Bool × 𝒴 × 𝒵`.

## References

* W. Miao and E. J. Tchetgen Tchetgen, *On varieties of doubly robust estimators under
  missingness not at random with a shadow variable*, Biometrika 103(2) (2016), 475–482,
  DOI 10.1093/biomet/asw016.
* W. Miao, L. Liu, Y. Li, E. J. Tchetgen Tchetgen and Z. Geng, *Identification and semiparametric
  efficiency theory of nonignorable missing data with a shadow variable*, ACM/IMS Journal of Data
  Science 1(2) (2024), DOI 10.1145/3592389.
* S. Wang, J. Shao and J. K. Kim, *An instrumental variable approach for identification and
  estimation with nonignorable nonresponse*, Statistica Sinica 24 (2014), 1097–1116.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality.MissingData

open MeasureTheory

variable {𝒴 𝒵 : Type*} [MeasurableSpace 𝒴] [MeasurableSpace 𝒵] [MeasurableSingletonClass 𝒴]
  [MeasurableSingletonClass 𝒵]

/-! ### Point masses -/

open scoped Classical in
/-- On a finite type with measurable singletons, the measure of a set is the sum of the point
masses in it. -/
lemma measureReal_eq_sum {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure α) [IsFiniteMeasure P] (s : Set α) :
    P.real s = ∑ ω, if ω ∈ s then P.real {ω} else 0 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, sum_measureReal_singleton]
  congr 1
  ext ω
  simp

open scoped Classical in
/-- The measure of a set inside the outcome fiber `Y = y`, as a sum over the shadow values. -/
lemma measureReal_eq_sum_fiber [Finite 𝒴] [Fintype 𝒵] (P : Measure (Bool × 𝒴 × 𝒵))
    [IsFiniteMeasure P]
    {s : Set (Bool × 𝒴 × 𝒵)} {y : 𝒴} (hs : s ⊆ {ω | ω.2.1 = y}) :
    P.real s = ∑ z, ((if (true, y, z) ∈ s then P.real {(true, y, z)} else 0) +
      (if (false, y, z) ∈ s then P.real {(false, y, z)} else 0)) := by
  have := Fintype.ofFinite 𝒴
  rw [measureReal_eq_sum P s]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib, Finset.sum_eq_single y]
  · rw [Finset.sum_add_distrib]
  · intro y' _ hy'
    have ht : ∀ z, (true, y', z) ∉ s := fun z h => hy' (hs h)
    have hf : ∀ z, (false, y', z) ∉ s := fun z h => hy' (hs h)
    simp [ht, hf]
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- The nonrespondent shadow margin: `P(R = false, Z = z) = ∑ y, P(R = false, Y = y, Z = z)`. -/
lemma measureReal_nonresponse_shadow [Fintype 𝒴] [Finite 𝒵] (P : Measure (Bool × 𝒴 × 𝒵))
    [IsFiniteMeasure P] (z : 𝒵) :
    P.real {ω | ω.1 = false ∧ ω.2.2 = z} = ∑ y, P.real {(false, y, z)} := by
  classical
  have := Fintype.ofFinite 𝒵
  rw [measureReal_eq_sum]
  simp [Fintype.sum_prod_type]

/-! ### Observed data -/

/-- The observed data of a full-data point `(r, y, z)`: the observed-data map `observedData R X Y`
with response event `R = {r = true}`, always-observed `X = z` and outcome `Y = y`. It records
`(z, Sum.inl y)` on response and `(z, Sum.inr ())` on nonresponse; the response indicator is
recovered by `observedData_snd_isLeft`. -/
noncomputable abbrev shadowObs : Bool × 𝒴 × 𝒵 → 𝒵 × (𝒴 ⊕ Unit) :=
  observedData {ω | ω.1 = true} (fun ω => ω.2.2) (fun ω => ω.2.1)

omit [MeasurableSingletonClass 𝒴] [MeasurableSingletonClass 𝒵] in
lemma measurable_shadowObs : Measurable (shadowObs : Bool × 𝒴 × 𝒵 → _) :=
  measurable_observedData (measurable_fst (measurableSet_singleton true)) measurable_snd.snd
    measurable_snd.fst

open scoped Classical in
private lemma measureReal_map_shadowObs_singleton [Fintype 𝒴] [Fintype 𝒵]
    (P : Measure (Bool × 𝒴 × 𝒵)) [IsFiniteMeasure P] (o : 𝒵 × (𝒴 ⊕ Unit)) :
    (P.map shadowObs).real {o} =
      (∑ y, ∑ z, if (z, Sum.inl y) = o then P.real {(true, y, z)} else 0) +
        ∑ z, if (z, Sum.inr ()) = o then ∑ y, P.real {(false, y, z)} else 0 := by
  have ho : MeasurableSet {o} := by
    obtain ⟨z, y | u⟩ := o
    · rw [← Set.singleton_prod_singleton, ← Set.image_singleton]
      exact (measurableSet_singleton z).prod (measurableSet_singleton y).inl_image
    · rw [← Set.singleton_prod_singleton, ← Set.image_singleton]
      exact (measurableSet_singleton z).prod (measurableSet_singleton u).inr_image
  rw [map_measureReal_apply measurable_shadowObs ho, measureReal_eq_sum]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, shadowObs, observedData, Set.mem_ofPred_eq,
    Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp

/-- **The observed-data law.** Two full-data laws have the same observed-data law exactly when
they agree on every respondent cell `(true, y, z)` and on every nonrespondent shadow margin
`P(R = false, Z = z)`. -/
theorem map_shadowObs_eq_iff [Fintype 𝒴] [Finite 𝒵] {P Q : Measure (Bool × 𝒴 × 𝒵)}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    P.map shadowObs = Q.map shadowObs ↔
      (∀ y z, P.real {(true, y, z)} = Q.real {(true, y, z)}) ∧
        ∀ z, ∑ y, P.real {(false, y, z)} = ∑ y, Q.real {(false, y, z)} := by
  classical
  have := Fintype.ofFinite 𝒵
  rw [ext_iff_measureReal_singleton]
  constructor
  · intro h
    refine ⟨fun y z => ?_, fun z => ?_⟩
    · have := h (z, Sum.inl y)
      simp only [measureReal_map_shadowObs_singleton, Prod.mk.injEq, Sum.inl.injEq, reduceCtorEq,
        and_false, ite_false, Finset.sum_const_zero, add_zero] at this
      simpa [ite_and, Finset.sum_ite_eq'] using this
    · have := h (z, Sum.inr ())
      simp only [measureReal_map_shadowObs_singleton, Prod.mk.injEq, reduceCtorEq, and_false,
        ite_false, Finset.sum_const_zero, zero_add, and_true] at this
      simpa [Finset.sum_ite_eq'] using this
  · rintro ⟨h1, h0⟩ o
    rw [measureReal_map_shadowObs_singleton, measureReal_map_shadowObs_singleton]
    simp only [h1, h0]

/-! ### The shadow assumption -/

/-- **Shadow variable assumption**: the shadow variable `Z` is conditionally independent of the
response given the outcome, `Z ⊥ R | Y`, stated by the discrete-fibre test `CondIndepDiscrete`.
Sufficient conditions for that test to be conditional independence given the outcome are a
finite measure on a standard Borel space and a countable outcome space with measurable
singletons: there `missingAtRandomCondIndepFun_iff_condIndepDiscrete` identifies it with
Mathlib's conditional independence of the response indicator and `Z` given `σ(Y)`. These
conditions are not necessary. Without them the test can hold vacuously: if the outcome is
diffuse, every fibre `{Y = y}` has mass zero, so every fibre identity reads `0 = 0` whether or
not `Z ⊥ R | Y`. -/
def ShadowVariable (P : Measure (Bool × 𝒴 × 𝒵)) : Prop :=
  CondIndepDiscrete P {ω | ω.1 = true} (fun ω => ω.2.2) (fun ω => ω.2.1)

/-- **Completeness**: the respondents' outcome given the shadow variable is complete. For every
`g`, if `∑ y, P(R = true, Y = y, Z = z) g(y) = 0` for all `z`, then `g = 0`. The masses are
`P.real` of singletons: for a finite measure with measurable singletons the condition reads
`E[g(Y) | Z = z, R = true] = 0` wherever defined, while `P.real` reads an infinite point mass
as `0`. -/
def ShadowComplete [Fintype 𝒴] (P : Measure (Bool × 𝒴 × 𝒵)) : Prop :=
  ∀ g : 𝒴 → ℝ, (∀ z, ∑ y, P.real {(true, y, z)} * g y = 0) → g = 0

/-- The nonresponse odds at the outcome value `y`: `P(R = false, Y = y) / P(R = true, Y = y)`,
each mass a sum of `P.real` of singletons. It is the odds for a finite measure with measurable
singletons (`P.real` reads an infinite point mass as `0`) and positive respondent mass
`∑ z, P.real {(true, y, z)}`. When nobody responds at `y` that sum is `0`, and division by zero
makes the value `0`, not the odds; `ShadowVariable.measureReal_false_eq` assumes the sum is
nonzero. -/
noncomputable def shadowOdds [Fintype 𝒵] (P : Measure (Bool × 𝒴 × 𝒵)) (y : 𝒴) : ℝ :=
  (∑ z, P.real {(false, y, z)}) / ∑ z, P.real {(true, y, z)}

open scoped Classical in
/-- The four events of the shadow assumption, as point masses. -/
private lemma shadowVariable_cells [Finite 𝒴] [Fintype 𝒵] (P : Measure (Bool × 𝒴 × 𝒵))
    [IsFiniteMeasure P] (B : Set 𝒵) (y : 𝒴) :
    P.real ({ω | ω.1 = true} ∩ (fun ω => ω.2.2) ⁻¹' B ∩ (fun ω => ω.2.1) ⁻¹' {y}) =
        ∑ z, (if z ∈ B then P.real {(true, y, z)} else 0) ∧
      P.real ((fun ω : Bool × 𝒴 × 𝒵 => ω.2.1) ⁻¹' {y}) =
        ∑ z, (P.real {(true, y, z)} + P.real {(false, y, z)}) ∧
      P.real ({ω | ω.1 = true} ∩ (fun ω => ω.2.1) ⁻¹' {y}) = ∑ z, P.real {(true, y, z)} ∧
      P.real ((fun ω => ω.2.2) ⁻¹' B ∩ (fun ω => ω.2.1) ⁻¹' {y}) =
        ∑ z, ((if z ∈ B then P.real {(true, y, z)} else 0) +
          (if z ∈ B then P.real {(false, y, z)} else 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [measureReal_eq_sum_fiber P (y := y)
      (s := {ω | ω.1 = true} ∩ (fun ω => ω.2.2) ⁻¹' B ∩ (fun ω => ω.2.1) ⁻¹' {y})
      (fun _ h => h.2)]
    simp
  · rw [measureReal_eq_sum_fiber P (y := y) (s := (fun ω => ω.2.1) ⁻¹' {y}) (fun _ h => h)]
    simp
  · rw [measureReal_eq_sum_fiber P (y := y) (s := {ω | ω.1 = true} ∩ (fun ω => ω.2.1) ⁻¹' {y})
      (fun _ h => h.2)]
    simp
  · rw [measureReal_eq_sum_fiber P (y := y)
      (s := (fun ω => ω.2.2) ⁻¹' B ∩ (fun ω => ω.2.1) ⁻¹' {y}) (fun _ h => h.2)]
    simp

/-- **Shadow factorization.** Under the shadow assumption,
`P(R = false, Y = y, Z = z) P(R = true, Y = y) = P(R = true, Y = y, Z = z) P(R = false, Y = y)`. -/
theorem ShadowVariable.measureReal_false_mul [Finite 𝒴] [Fintype 𝒵]
    {P : Measure (Bool × 𝒴 × 𝒵)} [IsFiniteMeasure P]
    (h : ShadowVariable P) (y : 𝒴) (z : 𝒵) :
    P.real {(false, y, z)} * ∑ z', P.real {(true, y, z')} =
      P.real {(true, y, z)} * ∑ z', P.real {(false, y, z')} := by
  classical
  have hci := h {z} (measurableSet_singleton z) y
  obtain ⟨h1, h2, h3, h4⟩ := shadowVariable_cells P {z} y
  rw [h1, h2, h3, h4] at hci
  simp only [Set.mem_singleton_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_add_distrib] at hci
  linear_combination -hci

/-- Under the shadow assumption, each nonrespondent cell is the odds times the matching
respondent cell, wherever the outcome value has respondents. -/
theorem ShadowVariable.measureReal_false_eq [Finite 𝒴] [Fintype 𝒵]
    {P : Measure (Bool × 𝒴 × 𝒵)} [IsFiniteMeasure P]
    (h : ShadowVariable P) {y : 𝒴} (hy : ∑ z, P.real {(true, y, z)} ≠ 0) (z : 𝒵) :
    P.real {(false, y, z)} = shadowOdds P y * P.real {(true, y, z)} := by
  have := h.measureReal_false_mul y z
  rw [shadowOdds]
  field_simp
  linarith

/-- **Converse of the shadow factorization.** If every nonrespondent cell is `b(y)` times the
matching respondent cell, the shadow assumption holds. -/
theorem shadowVariable_of_odds [Finite 𝒴] [Finite 𝒵] {P : Measure (Bool × 𝒴 × 𝒵)}
    [IsFiniteMeasure P] (b : 𝒴 → ℝ)
    (hb : ∀ y z, P.real {(false, y, z)} = b y * P.real {(true, y, z)}) : ShadowVariable P := by
  classical
  have := Fintype.ofFinite 𝒵
  intro B _ y
  obtain ⟨h1, h2, h3, h4⟩ := shadowVariable_cells P B y
  rw [h1, h2, h3, h4]
  simp only [hb]
  have e2 : ∑ z, (P.real {(true, y, z)} + b y * P.real {(true, y, z)}) =
      (1 + b y) * ∑ z, P.real {(true, y, z)} := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  have e4 : ∑ z, ((if z ∈ B then P.real {(true, y, z)} else 0) +
      (if z ∈ B then b y * P.real {(true, y, z)} else 0)) =
      (1 + b y) * ∑ z, (if z ∈ B then P.real {(true, y, z)} else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> ring
  rw [e2, e4]
  ring

omit [MeasurableSingletonClass 𝒴] [MeasurableSingletonClass 𝒵] in
/-- **Completeness forces respondents at every outcome value**: the singleton masses
`P.real {(true, y, z)}` do not sum to `0`. When singletons are measurable, the sum is
`P(R = true, Y = y)`. -/
theorem ShadowComplete.sum_ne_zero [Fintype 𝒴] [Fintype 𝒵]
    {P : Measure (Bool × 𝒴 × 𝒵)} [IsFiniteMeasure P]
    (hc : ShadowComplete P) (y : 𝒴) : ∑ z, P.real {(true, y, z)} ≠ 0 := by
  classical
  intro h0
  have hzero : ∀ z, P.real {(true, y, z)} = 0 := fun z =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => measureReal_nonneg)).1 h0 z (Finset.mem_univ z)
  have := congrFun (hc (fun y' => if y' = y then 1 else 0) fun z => by simp [hzero z]) y
  simp at this

/-- The odds solve the **observed integral equation**
`∑ y, a(y) P(R = true, Y = y, Z = z) = P(R = false, Z = z)`. -/
theorem ShadowVariable.sum_shadowOdds_mul [Fintype 𝒴] [Fintype 𝒵]
    {P : Measure (Bool × 𝒴 × 𝒵)} [IsFiniteMeasure P]
    (h : ShadowVariable P) (hc : ShadowComplete P) (z : 𝒵) :
    ∑ y, shadowOdds P y * P.real {(true, y, z)} = ∑ y, P.real {(false, y, z)} :=
  Finset.sum_congr rfl fun y _ => (h.measureReal_false_eq (hc.sum_ne_zero y) z).symm

/-- **Uniqueness of the odds.** Under completeness, the odds are the only solution of the
observed integral equation. -/
theorem ShadowComplete.eq_shadowOdds [Fintype 𝒴] [Fintype 𝒵]
    {P : Measure (Bool × 𝒴 × 𝒵)} [IsFiniteMeasure P]
    (h : ShadowVariable P) (hc : ShadowComplete P) {g : 𝒴 → ℝ}
    (hg : ∀ z, ∑ y, g y * P.real {(true, y, z)} = ∑ y, P.real {(false, y, z)}) :
    g = shadowOdds P := by
  have := hc (fun y => g y - shadowOdds P y) fun z => by
    have e1 := hg z
    have e2 := h.sum_shadowOdds_mul hc z
    simp only [mul_comm (g _) _] at e1
    simp only [mul_comm (shadowOdds P _) _] at e2
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  funext y
  exact sub_eq_zero.1 (congrFun this y)

/-! ### Identification -/

/-- **Identification with a shadow variable** (Miao–Tchetgen Tchetgen). Two full-data laws that
satisfy the shadow assumption and have the same observed-data law are equal, provided one of
them is complete. -/
theorem eq_of_map_shadowObs_eq [Fintype 𝒴] [Finite 𝒵] {P Q : Measure (Bool × 𝒴 × 𝒵)}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hP : ShadowVariable P) (hQ : ShadowVariable Q)
    (hc : ShadowComplete P)
    (hobs : P.map shadowObs = Q.map shadowObs) : P = Q := by
  have := Fintype.ofFinite 𝒵
  obtain ⟨h1, h0⟩ := map_shadowObs_eq_iff.1 hobs
  have hcQ : ShadowComplete Q := fun g hg => hc g fun z => by simpa [h1] using hg z
  have hodds : shadowOdds Q = shadowOdds P := hc.eq_shadowOdds hP fun z => by
    rw [h0 z, ← hQ.sum_shadowOdds_mul hcQ z]
    simp only [h1]
  rw [ext_iff_measureReal_singleton]
  rintro ⟨_ | _, y, z⟩
  · rw [hP.measureReal_false_eq (hc.sum_ne_zero y), hQ.measureReal_false_eq (hcQ.sum_ne_zero y),
      hodds, h1]
  · exact h1 y z

/-- **Every outcome integral is identified**: for finite measures `P` and `Q` satisfying the
hypotheses of `eq_of_map_shadowObs_eq`, the integrals of `f(Y)` under `P` and `Q` are equal. When
`P` and `Q` are probability measures these are the means of `f(Y)`. Contrast
`exists_map_obsRY_eq_integral_eq`, where without a shadow variable the identified set of the mean
is all of `ℝ`. -/
theorem integral_eq_of_map_shadowObs_eq [Fintype 𝒴] [Finite 𝒵]
    {P Q : Measure (Bool × 𝒴 × 𝒵)}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hP : ShadowVariable P) (hQ : ShadowVariable Q)
    (hc : ShadowComplete P) (hobs : P.map shadowObs = Q.map shadowObs) (f : 𝒴 → ℝ) :
    ∫ ω, f ω.2.1 ∂P = ∫ ω, f ω.2.1 ∂Q := by
  rw [eq_of_map_shadowObs_eq hP hQ hc hobs]

/-! ### Completeness is necessary -/

/-- **Completeness cannot be dropped.** Let `P` satisfy the shadow assumption with overlap,
`0 < P(R = true, Y = y)` and `0 < P(R = false, Y = y)` for every `y`. If `P` is not complete,
another probability law that satisfies the shadow assumption has the same observed-data law as
`P` and differs from it. -/
theorem exists_ne_map_shadowObs_eq_of_not_shadowComplete [Fintype 𝒴] [Fintype 𝒵]
    {P : Measure (Bool × 𝒴 × 𝒵)} [IsProbabilityMeasure P] (hP : ShadowVariable P)
    (hresp : ∀ y, ∑ z, P.real {(true, y, z)} ≠ 0) (hnonresp : ∀ y, ∑ z, P.real {(false, y, z)} ≠ 0)
    (hnc : ¬ ShadowComplete P) :
    ∃ Q : Measure (Bool × 𝒴 × 𝒵), IsProbabilityMeasure Q ∧ ShadowVariable Q ∧
      Q.map shadowObs = P.map shadowObs ∧ Q ≠ P := by
  classical
  simp only [ShadowComplete, not_forall, exists_prop] at hnc
  obtain ⟨g, hg, hg0⟩ := hnc
  -- The odds are positive.
  have hpos : ∀ y, 0 < shadowOdds P y := fun y =>
    div_pos ((Finset.sum_nonneg fun _ _ => measureReal_nonneg).lt_of_ne (hnonresp y).symm)
      ((Finset.sum_nonneg fun _ _ => measureReal_nonneg).lt_of_ne (hresp y).symm)
  -- A small perturbation of the odds along `g` keeps them positive.
  have hev : ∀ᶠ ε in nhds (0 : ℝ), ∀ y, ε * |g y| < shadowOdds P y := by
    refine Filter.eventually_all.2 fun y => ?_
    have ht : Filter.Tendsto (fun ε : ℝ => ε * |g y|) (nhds 0) (nhds (0 * |g y|)) :=
      Filter.tendsto_id.mul_const _
    rw [zero_mul] at ht
    exact ht.eventually (gt_mem_nhds (hpos y))
  obtain ⟨δ, hδ, hδp⟩ := Metric.eventually_nhds_iff.1 hev
  set ε := δ / 2
  have hεpos : 0 < ε := half_pos hδ
  have hε : ∀ y, ε * |g y| < shadowOdds P y := hδp (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hεpos]
    exact half_lt_self hδ)
  set b : 𝒴 → ℝ := fun y => shadowOdds P y + ε * g y
  have hb : ∀ y, 0 < b y := fun y => by
    have h1 := hε y
    have h2 : -(ε * |g y|) ≤ ε * g y := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_abs_le _) (le_of_lt hεpos)
    simp only [b]
    linarith
  set w : Bool × 𝒴 × 𝒵 → ℝ := fun ω =>
    if ω.1 then P.real {ω} else b ω.2.1 * P.real {(true, ω.2.1, ω.2.2)}
  have hw : ∀ ω, 0 ≤ w ω := by
    rintro ⟨_ | _, y, z⟩
    · exact mul_nonneg (hb y).le measureReal_nonneg
    · exact measureReal_nonneg
  set Q := weightLaw w
  have hQ1 : ∀ y z, Q.real {(true, y, z)} = P.real {(true, y, z)} := fun y z => by
    rw [measureReal_weightLaw_singleton hw]
    simp [w]
  have hQ0 : ∀ y z, Q.real {(false, y, z)} = b y * P.real {(true, y, z)} := fun y z => by
    rw [measureReal_weightLaw_singleton hw]
    simp [w]
  -- The nonrespondent shadow margins are unchanged, because `g` solves the homogeneous equation.
  have hmargin : ∀ z, ∑ y, Q.real {(false, y, z)} = ∑ y, P.real {(false, y, z)} := fun z => by
    simp only [hQ0, b, add_mul, Finset.sum_add_distrib, mul_assoc]
    rw [← Finset.mul_sum]
    have : ∑ y, g y * P.real {(true, y, z)} = 0 := by
      simpa only [mul_comm] using hg z
    rw [this, mul_zero, add_zero]
    exact Finset.sum_congr rfl fun y _ => (hP.measureReal_false_eq (hresp y) z).symm
  have hobs : Q.map shadowObs = P.map shadowObs := map_shadowObs_eq_iff.2 ⟨hQ1, hmargin⟩
  -- Total mass: the observed-data laws agree, and the observed data map is total.
  have hprob : IsProbabilityMeasure Q := by
    constructor
    have hmass : (Q.map shadowObs) Set.univ = (P.map shadowObs) Set.univ := by rw [hobs]
    rwa [Measure.map_apply measurable_shadowObs MeasurableSet.univ,
      Measure.map_apply measurable_shadowObs MeasurableSet.univ, Set.preimage_univ,
      measure_univ (μ := P)] at hmass
  refine ⟨Q, hprob, shadowVariable_of_odds b fun y z => by rw [hQ0, hQ1], hobs, fun hQP => hg0 ?_⟩
  funext y
  obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hresp y)
  have h1 : Q.real {(false, y, z)} = P.real {(false, y, z)} := by rw [hQP]
  rw [hQ0, hP.measureReal_false_eq (hresp y)] at h1
  have : ε * g y * P.real {(true, y, z)} = 0 := by
    simp only [b] at h1
    linarith
  simpa [hεpos.ne', hz] using this

end MathlibExt.Probability.Causality.MissingData
