/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.ShadowVariables

/-!
# Tests for shadow-variable identification

* Non-vacuity of the identification theorem: an explicit law on `Bool × Bool × Bool` (binary
  outcome, binary shadow variable) that satisfies the shadow assumption and completeness, with
  response depending on the outcome even given the shadow variable (missing not at random).
  Every hypothesis is checked from the point masses, not through the theorem.
* The nonresponse odds of that law, computed from the definition.
* Boundary, trivial shadow variable: with `𝒵 = Unit` the shadow assumption always holds, and the
  self-masking pair of `MNARCounterexample` (outcome constant versus outcome equal to response)
  has the same observed-data law and different full-data laws; completeness fails.
* Non-vacuity of the necessity theorem: response independent of a binary outcome with a trivial
  shadow variable has overlap and is not complete.
-/

@[expose] public section

open MeasureTheory MathlibExt.Probability MathlibExt.Probability.Causality
  MathlibExt.Probability.Causality.MissingData

namespace MathlibExtTest.Probability.Causality.MissingData.Shadow

/-! ### An identified MNAR law -/

/-- Point masses (times `32`) of a law with a fair-coin outcome `Y`, response probability `1/4`
when `Y = true` and `3/4` when `Y = false`, and shadow variable `Z` equal to `Y` with probability
`3/4`, independently of the response given `Y`. Coordinates are `(r, y, z)`. -/
noncomputable def w : Bool × Bool × Bool → ℝ
  | (true, true, true) => 3 / 32
  | (true, true, false) => 1 / 32
  | (false, true, true) => 9 / 32
  | (false, true, false) => 3 / 32
  | (true, false, true) => 3 / 32
  | (true, false, false) => 9 / 32
  | (false, false, true) => 1 / 32
  | (false, false, false) => 3 / 32

lemma w_nonneg : ∀ ω, 0 ≤ w ω := by
  rintro ⟨_ | _, _ | _, _ | _⟩ <;> norm_num [w]

/-- The identified MNAR law. -/
noncomputable abbrev mnarLaw : Measure (Bool × Bool × Bool) := weightLaw w

@[simp] lemma mnarLaw_singleton (ω : Bool × Bool × Bool) : mnarLaw.real {ω} = w ω :=
  measureReal_weightLaw_singleton w_nonneg ω

open scoped Classical in
lemma mnarLaw_real (s : Set (Bool × Bool × Bool)) :
    mnarLaw.real s = ∑ ω, if ω ∈ s then w ω else 0 := by
  rw [measureReal_eq_sum]
  simp

instance : IsProbabilityMeasure mnarLaw := by
  constructor
  have h : mnarLaw.real Set.univ = 1 := by
    rw [measureReal_eq_sum]
    simp [Fintype.sum_prod_type, w]
    norm_num
  exact (ENNReal.toReal_eq_one_iff _).1 h

/-- The shadow assumption, checked on every set `B` of shadow values from the point masses. -/
lemma shadowVariable_mnarLaw : ShadowVariable mnarLaw := by
  classical
  intro B _ y
  simp only [mnarLaw_real]
  by_cases ht : true ∈ B <;> by_cases hf : false ∈ B <;> cases y <;>
    simp [Fintype.sum_prod_type, w, ht, hf] <;> norm_num

/-- Completeness, checked from the point masses: the respondent matrix
`((3, 3), (1, 9)) / 32` (rows `z`, columns `y = true, false`) is invertible. -/
lemma shadowComplete_mnarLaw : ShadowComplete mnarLaw := by
  intro g hg
  have h1 := hg true
  have h2 := hg false
  simp [w] at h1 h2
  funext y
  cases y <;> simp <;> linarith

/-- The law is MNAR even given the shadow variable: response is not conditionally independent of
the outcome given `Z` (at `Z = true`, `3 · 16 ≠ 6 · 12`). -/
lemma not_condIndepDiscrete_mnarLaw :
    ¬ CondIndepDiscrete mnarLaw {ω | ω.1 = true} (fun ω => ω.2.1) (fun ω => ω.2.2) := by
  classical
  intro h
  have := h {true} (measurableSet_singleton true) true
  simp only [mnarLaw_real] at this
  simp [Fintype.sum_prod_type, w] at this
  norm_num at this

/-- The nonresponse odds, from the definition: `3` at `Y = true`, `1/3` at `Y = false`. -/
example : shadowOdds mnarLaw true = 3 ∧ shadowOdds mnarLaw false = 1 / 3 := by
  simp [shadowOdds, w]
  norm_num

/-- **Non-vacuity of identification**: every shadow law with the observed-data law of `mnarLaw`
is `mnarLaw`. -/
example (Q : Measure (Bool × Bool × Bool)) [IsFiniteMeasure Q] (hQ : ShadowVariable Q)
    (hobs : mnarLaw.map shadowObs = Q.map shadowObs) : mnarLaw = Q :=
  eq_of_map_shadowObs_eq shadowVariable_mnarLaw hQ shadowComplete_mnarLaw hobs

/-- The outcome mean is identified. -/
example (Q : Measure (Bool × Bool × Bool)) [IsFiniteMeasure Q] (hQ : ShadowVariable Q)
    (hobs : mnarLaw.map shadowObs = Q.map shadowObs) :
    ∫ ω, (if ω.2.1 then (1 : ℝ) else 0) ∂mnarLaw = ∫ ω, (if ω.2.1 then (1 : ℝ) else 0) ∂Q :=
  integral_eq_of_map_shadowObs_eq shadowVariable_mnarLaw hQ shadowComplete_mnarLaw hobs
    (fun y => if y then 1 else 0)

/-! ### Boundary: a trivial shadow variable -/

/-- A constant shadow variable satisfies the shadow assumption under every law. -/
lemma shadowVariable_unit (P : Measure (Bool × Bool × Unit)) : ShadowVariable P := by
  intro B _ y
  by_cases h : () ∈ B
  · have hB : (fun ω : Bool × Bool × Unit => ω.2.2) ⁻¹' B = Set.univ := by
      ext ω; simp [h]
    rw [hB, Set.inter_univ, Set.univ_inter]
  · have hB : (fun ω : Bool × Bool × Unit => ω.2.2) ⁻¹' B = ∅ := by
      ext ω; simp [h]
    simp [hB]

/-- `MNARCounterexample.constOutcomeLaw` with a trivial shadow: fair-coin response, `Y = true`. -/
noncomputable def constLaw : Measure (Bool × Bool × Unit) :=
  (2⁻¹ : ENNReal) • (Measure.dirac (true, true, ()) + Measure.dirac (false, true, ()))

/-- `MNARCounterexample.selfMaskingLaw` with a trivial shadow: `Y = true` exactly on response. -/
noncomputable def maskLaw : Measure (Bool × Bool × Unit) :=
  (2⁻¹ : ENNReal) • (Measure.dirac (true, true, ()) + Measure.dirac (false, false, ()))

instance : IsFiniteMeasure constLaw := by
  constructor
  simp [constLaw, ENNReal.inv_two_add_inv_two]

instance : IsFiniteMeasure maskLaw := by
  constructor
  simp [maskLaw, ENNReal.inv_two_add_inv_two]

/-- The pair has the same observed-data law, computed by pushing the point masses forward. -/
lemma map_shadowObs_constLaw : constLaw.map shadowObs = maskLaw.map shadowObs := by
  have hm : Measurable (shadowObs : Bool × Bool × Unit → Unit × (Bool ⊕ Unit)) :=
    measurable_shadowObs
  rw [constLaw, maskLaw, Measure.map_smul, Measure.map_smul, Measure.map_add _ _ hm,
    Measure.map_add _ _ hm, Measure.map_dirac' hm, Measure.map_dirac' hm, Measure.map_dirac' hm]
  · simp [shadowObs, observedData]
  all_goals exact hm.aemeasurable

/-- The pair differs at the nonrespondent cell `(false, true, ())`. -/
lemma constLaw_ne_maskLaw : constLaw ≠ maskLaw := by
  intro h
  have := congrArg (fun μ : Measure (Bool × Bool × Unit) => μ {(false, true, ())}) h
  simp [constLaw, maskLaw] at this

/-- Without completeness, identification fails: two shadow laws with the same observed-data law
are different. -/
example : ShadowVariable constLaw ∧ ShadowVariable maskLaw ∧
    constLaw.map shadowObs = maskLaw.map shadowObs ∧ constLaw ≠ maskLaw :=
  ⟨shadowVariable_unit _, shadowVariable_unit _, map_shadowObs_constLaw, constLaw_ne_maskLaw⟩

/-- `constLaw` is not complete: it has no respondents with `Y = false`. -/
example : ¬ ShadowComplete constLaw := by
  intro hc
  have := congrFun (hc (fun y => if y then 0 else 1) fun z => by
    simp [constLaw, Measure.real]) false
  simp at this

/-- The characterization `map_shadowObs_eq_iff` agrees with the direct computation. -/
example : (∀ y z, constLaw.real {(true, y, z)} = maskLaw.real {(true, y, z)}) ∧
    ∀ z, ∑ y, constLaw.real {(false, y, z)} = ∑ y, maskLaw.real {(false, y, z)} :=
  map_shadowObs_eq_iff.1 map_shadowObs_constLaw

/-! ### Non-vacuity of the necessity theorem -/

/-- Response a fair coin independent of a fair-coin outcome, with a trivial shadow variable. -/
noncomputable abbrev indepLaw : Measure (Bool × Bool × Unit) := weightLaw fun _ => 1 / 4

@[simp] lemma indepLaw_singleton (ω : Bool × Bool × Unit) : indepLaw.real {ω} = 1 / 4 :=
  measureReal_weightLaw_singleton (fun _ => by norm_num) ω

instance : IsProbabilityMeasure indepLaw := by
  constructor
  have h : indepLaw.real Set.univ = 1 := by
    rw [measureReal_eq_sum]
    simp
  exact (ENNReal.toReal_eq_one_iff _).1 h

lemma not_shadowComplete_indepLaw : ¬ ShadowComplete indepLaw := by
  intro hc
  have := congrFun (hc (fun y => if y then 1 else -1) fun z => by simp) true
  simp at this

/-- The hypotheses of `exists_ne_map_shadowObs_eq_of_not_shadowComplete` hold at `indepLaw`. -/
example : ∃ Q : Measure (Bool × Bool × Unit), IsProbabilityMeasure Q ∧ ShadowVariable Q ∧
    Q.map shadowObs = indepLaw.map shadowObs ∧ Q ≠ indepLaw :=
  exists_ne_map_shadowObs_eq_of_not_shadowComplete (shadowVariable_unit _)
    (fun _ => by simp) (fun _ => by simp) not_shadowComplete_indepLaw

end MathlibExtTest.Probability.Causality.MissingData.Shadow
