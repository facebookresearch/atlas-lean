/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.Definitions

/-!
# Tests for missing-data mechanisms

The sample space is two fair coins, `Ω = Bool × Bool`.

* The observed-data map: values on a respondent and a nonrespondent, and two different outcomes
  with the same observed data (the outcome of a nonrespondent is not recorded).
* MCAR witness: the response is the first coin and the outcome the second, with a constant
  covariate. MCAR holds with response probability `1/2`, so MAR holds by the bridge.
* MAR without MCAR: the response is the first coin and so is the covariate. MAR holds (the response
  is a function of the covariate) and MCAR fails, so the hierarchy is strict.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality
  MathlibExt.Probability.Causality.MissingData

namespace MathlibExtTest.Probability.Causality.MissingData

/-! ### Two fair coins -/

/-- A fair coin. -/
noncomputable def coin : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

lemma coin_apply_singleton (b : Bool) : coin {b} = 2⁻¹ := by
  cases b <;> simp [coin]

instance : IsProbabilityMeasure coin := by
  constructor
  rw [show (Set.univ : Set Bool) = {true} ∪ {false} by ext b; cases b <;> simp,
    measure_union (by simp) (measurableSet_singleton _), coin_apply_singleton,
    coin_apply_singleton, ENNReal.inv_two_add_inv_two]

lemma coin_singleton (b : Bool) : coin.real {b} = 1 / 2 := by
  rw [measureReal_def, coin_apply_singleton]; simp

lemma coin_univ : coin.real Set.univ = 1 := by
  rw [measureReal_def, measure_univ, ENNReal.toReal_one]

/-- Two independent fair coins. -/
noncomputable def coins : Measure (Bool × Bool) :=
  coin.prod coin

instance : IsProbabilityMeasure coins := by
  unfold coins; infer_instance

lemma coins_prod (A B : Set Bool) : coins.real (A ×ˢ B) = coin.real A * coin.real B := by
  rw [measureReal_def, coins, Measure.prod_prod, ENNReal.toReal_mul, measureReal_def,
    measureReal_def]

/-- The event that the first coin shows heads (`true`), used as the response event. -/
def heads₁ : Set (Bool × Bool) :=
  Prod.fst ⁻¹' {true}

lemma heads₁_eq : heads₁ = {true} ×ˢ Set.univ := by
  ext ω; simp [heads₁]

lemma measurableSet_heads₁ : MeasurableSet heads₁ :=
  measurable_fst (measurableSet_singleton true)

lemma coins_heads₁ : coins.real heads₁ = 1 / 2 := by
  rw [heads₁_eq, coins_prod, coin_singleton, coin_univ, mul_one]

/-! ### The observed-data map -/

/-- A respondent shows the covariate and the outcome. -/
example : observedData heads₁ Prod.fst Prod.snd (true, false) = (true, Sum.inl false) :=
  observedData_of_mem _ _ rfl

/-- A nonrespondent shows the covariate and the missing marker. -/
example : observedData heads₁ Prod.fst Prod.snd (false, true) = (false, Sum.inr ()) :=
  observedData_of_notMem _ _ (by simp [heads₁])

example : ¬(observedData heads₁ Prod.fst Prod.snd (false, true)).2.isLeft = true := by
  rw [observedData_snd_isLeft]; simp [heads₁]

/-- Two outcomes that differ only on nonrespondents give the same observed data, although they
are different full-data outcomes. -/
example : observedData heads₁ Prod.fst Prod.snd = observedData heads₁ Prod.fst
      (fun ω => ω.1 && ω.2) ∧
    (Prod.snd : Bool × Bool → Bool) ≠ fun ω => ω.1 && ω.2 := by
  refine ⟨observedData_congr _ fun ω h => ?_, fun h => ?_⟩
  · simp only [heads₁, Set.mem_preimage, Set.mem_singleton_iff] at h
    simp [h]
  · simpa using congrFun h (false, true)

example : Measurable (observedData heads₁ Prod.fst Prod.snd) :=
  measurable_observedData measurableSet_heads₁ measurable_fst measurable_snd

/-- Boundary: with no respondents the observed data never contain an outcome. -/
example (ω : Bool × Bool) :
    observedData (∅ : Set (Bool × Bool)) Prod.fst Prod.snd ω = (ω.1, Sum.inr ()) :=
  observedData_of_notMem _ _ (Set.notMem_empty ω)

/-! ### An MCAR witness -/

/-- **Non-vacuity of MCAR**: the response is the first coin, the outcome the second, and the
covariate constant. The response probability is `1/2` (`coins_heads₁`). -/
theorem mcar_coins : MissingCompletelyAtRandom coins heads₁ (fun _ => ()) Prod.snd := by
  rw [missingCompletelyAtRandom_iff measurableSet_heads₁]
  intro t _
  set S : Set Bool := {b | ((), b) ∈ t}
  have h1 : (fun ω : Bool × Bool => ((), ω.2)) ⁻¹' t = Set.univ ×ˢ S := by
    ext ω; simp [S]
  have h2 : heads₁ ∩ (fun ω : Bool × Bool => ((), ω.2)) ⁻¹' t = {true} ×ˢ S := by
    ext ω; simp [heads₁, S]
  rw [h2, heads₁_eq, h1, coins_prod, coins_prod, coins_prod, coin_univ]
  ring

/-- The same witness through the `CondIndepDiscrete` form of MCAR. -/
example : CondIndepDiscrete coins heads₁ (fun ω => ((), ω.2)) (fun _ => ()) :=
  (missingCompletelyAtRandom_iff_condIndepDiscrete measurableSet_heads₁).1 mcar_coins

example : CondIndepDiscrete coins heads₁ Prod.snd (fun _ => ()) :=
  mcar_coins.condIndepDiscrete

/-- MCAR implies MAR on the witness. -/
example : MissingAtRandom coins heads₁ (fun _ => ()) measurable_const Prod.snd :=
  mcar_coins.missingAtRandom measurableSet_heads₁ measurable_const measurable_snd

/-! ### MAR without MCAR -/

/-- The response is the covariate (the first coin), so it is a function of the covariate. -/
theorem condIndepDiscrete_fst : CondIndepDiscrete coins heads₁ Prod.snd Prod.fst := by
  intro B _ w
  cases w
  · have h1 : heads₁ ∩ Prod.snd ⁻¹' B ∩ Prod.fst ⁻¹' {false} = ∅ := by
      ext ω; simp only [heads₁, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false]; grind
    have h2 : heads₁ ∩ Prod.fst ⁻¹' {false} = ∅ := by
      ext ω; simp only [heads₁, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false]; grind
    simp [h1, h2]
  · have h1 : heads₁ ∩ Prod.snd ⁻¹' B ∩ Prod.fst ⁻¹' {true} =
        Prod.snd ⁻¹' B ∩ Prod.fst ⁻¹' {true} := by
      ext ω; simp only [heads₁, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      grind
    have h2 : heads₁ ∩ Prod.fst ⁻¹' {true} = Prod.fst ⁻¹' {true} := by
      ext ω; simp [heads₁]
    rw [h1, h2, mul_comm]

/-- **MAR holds** for the response equal to the covariate. -/
theorem mar_fst : MissingAtRandom coins heads₁ Prod.fst measurable_fst Prod.snd :=
  (missingAtRandom_iff_condIndepDiscrete measurableSet_heads₁ measurable_fst measurable_snd).2
    condIndepDiscrete_fst

/-- **MCAR fails** for the response equal to the covariate: `P(R, X = true) = 1/2` while
`P(R) P(X = true) = 1/4`. So MAR is strictly weaker than MCAR. -/
theorem not_mcar_fst : ¬MissingCompletelyAtRandom coins heads₁ Prod.fst Prod.snd := by
  rw [missingCompletelyAtRandom_iff measurableSet_heads₁]
  intro h
  have key := h ({true} ×ˢ Set.univ) ((measurableSet_singleton true).prod MeasurableSet.univ)
  have hZ : (fun ω : Bool × Bool => (ω.1, ω.2)) ⁻¹' ({true} ×ˢ Set.univ) = heads₁ := by
    rw [heads₁_eq]; ext ω; simp
  rw [hZ, Set.inter_self, coins_heads₁] at key
  norm_num at key

/-- The conditional probability of response given the covariate is the propensity. -/
example : coins⟦heads₁ | MeasurableSpace.comap Prod.fst inferInstance⟧ =ᵐ[coins]
    fun ω => propensity coins heads₁ Prod.fst ω.1 :=
  condExp_indicator_comap_ae_eq measurable_fst measurableSet_heads₁

end MathlibExtTest.Probability.Causality.MissingData
