/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Tests for causal identification with potential outcomes

* A fair coin as the probability space: propensity values (including the junk value at a
  covariate value of probability zero), a witness of strong ignorability, Theorem 2 of
  Rosenbaum & Rubin on it, and the IPW identities (finite and general covariate) on it.
* Neyman's results: junk values outside the domain (no control units; one unit per arm), a
  direct computation of unbiasedness on two units, and instances of the variance results.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality

namespace MathlibExtTest.Probability.Causality

/-! ### A fair coin as the probability space -/

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

/-! ### Propensity score -/

/-- Junk value: the propensity at a value of probability zero is `0`. -/
example : propensity (Measure.dirac true) {true} id false = 0 := by
  simp [propensity]

/-- With a single covariate value and a fair coin as the treatment, the propensity is `1/2`. -/
example : propensity coin {true} (fun _ => ()) () = 1 / 2 := by
  simp only [propensity, Set.preimage_const, Set.mem_singleton_iff, ↓reduceIte, Set.inter_univ,
    coin_singleton, coin_univ, div_one]

/-- **Non-vacuity**: strong ignorability holds for a fair-coin treatment, a constant covariate
and a constant potential outcome. -/
theorem stronglyIgnorable_coin (c : ℝ) :
    StronglyIgnorable coin {true} (fun _ => c) (fun _ => ()) := by
  refine ⟨fun B _ w => ?_, fun w _ => ?_⟩
  · by_cases hc : c ∈ B <;> simp [hc]
  · simp only [propensity, Set.preimage_const, Set.mem_singleton_iff, ↓reduceIte,
      Set.inter_univ, coin_singleton, coin_univ]
    norm_num

/-- Theorem 2 on the witness: with a single covariate value every function of it is a balancing
score. -/
example (b : Unit → Bool) :
    CondIndepDiscrete coin {true} (fun _ : Bool => ()) (fun ω => b ((fun _ : Bool => ()) ω)) :=
  (condIndepDiscrete_comp_iff (measurableSet_singleton true) measurable_const b).2
    fun x x' _ _ _ => by rw [Subsingleton.elim x x']

/-- The IPW identity on the witness: `E[1_T Y / e(X)] = E[Y₁] = c`. -/
example (c : ℝ) :
    ∫ ω, ({true} : Set Bool).indicator
        (fun ω => observed {true} (fun _ => 0) (fun _ => c) ω /
          propensity coin {true} (fun _ => ()) ()) ω ∂coin = c := by
  rw [integral_ipw_treated (measurableSet_singleton true) measurable_const measurable_const
    (integrable_const c) (stronglyIgnorable_coin c), integral_const, coin_univ, smul_eq_mul,
    one_mul]

/-- **Non-vacuity** of the general IPW identity: the trivial σ-algebra, a fair-coin treatment and
a constant potential outcome satisfy conditional mean independence and strong overlap. -/
example (c : ℝ) :
    ∫ ω, ({true} : Set Bool).indicator
        (fun ω => observed {true} (fun _ => 0) (fun _ => c) ω /
          coin[({true} : Set Bool).indicator 1 | ⊥] ω) ω ∂coin = c := by
  have hT : ∫ ω, ({true} : Set Bool).indicator (1 : Bool → ℝ) ω ∂coin = 1 / 2 := by
    rw [Pi.one_def, integral_indicator_const _ (measurableSet_singleton true), coin_singleton,
      smul_eq_mul, mul_one]
  rw [integral_ipw_treated_condExp bot_le (measurableSet_singleton true) (integrable_const c)
    _ (by norm_num : (0 : ℝ) < 1 / 2)]
  · rw [integral_const, coin_univ, one_smul]
  · refine Filter.Eventually.of_forall fun ω => ?_
    simp only [condExp_bot]
    rw [hT]
  · refine Filter.Eventually.of_forall fun ω => ?_
    simp only [condExp_bot]
    rw [hT, integral_indicator_const _ (measurableSet_singleton true), coin_singleton,
      integral_const, coin_univ, one_smul, smul_eq_mul, mul_comm]

/-! ### Neyman's finite-population results -/

/-- Junk value: with every unit treated there is no control group, and the difference in means
is the treated mean (the control mean of the empty set is `0 / 0 = 0`). -/
example (y₀ y₁ : Fin 3 → ℝ) :
    diffInMeans y₀ y₁ Finset.univ = sampleMean y₁ Finset.univ := by
  simp [diffInMeans, sampleMean]

/-- Junk value: the sample variance of a single unit is `0 / 0 = 0`, which is why Neyman's
estimator needs at least two units per arm. -/
example (y : Fin 3 → ℝ) : sampleVar y {0} = 0 := by
  simp [sampleVar, sampleMean]

/-- A direct check of unbiasedness on two units with one treated: the two assignments give
estimates `3 - 1 = 2` and `5 - 1 = 4`, whose mean is the ATE `3`. -/
example : randExp 1 (diffInMeans ![1, 1] ![3, 5]) = 3 := by
  rw [randExp, Finset.powersetCard_one, Finset.sum_map]
  simp [diffInMeans, sampleMean, Fin.sum_univ_two, Finset.compl_singleton]
  norm_num

/-- The same value from the theorem: the ATE of `y₁ = (3, 5)`, `y₀ = (1, 1)`. -/
example : randExp 1 (diffInMeans ![1, 1] ![3, 5]) = 3 := by
  rw [randExp_diffInMeans _ _ le_rfl (by simp)]
  simp [ate, popMean, Fin.sum_univ_two]
  norm_num

/-- **Non-vacuity** of the hypotheses of the variance results: four units, two treated. -/
example (y₀ y₁ : Fin 4 → ℝ) :
    randExp 2 (fun S => (diffInMeans y₀ y₁ S - ate y₀ y₁) ^ 2) ≤ randExp 2 (neymanVar y₀ y₁) :=
  (randVar_le_randExp_neymanVar y₀ y₁ le_rfl (by simp)).1

/-- With a constant treatment effect Neyman's estimator is unbiased for the variance. -/
example (y₀ : Fin 4 → ℝ) (c : ℝ) :
    randExp 2 (fun S => (diffInMeans y₀ (fun i => y₀ i + c) S - ate y₀ (fun i => y₀ i + c)) ^ 2) =
      randExp 2 (neymanVar y₀ (fun i => y₀ i + c)) :=
  (randVar_le_randExp_neymanVar y₀ _ le_rfl (by simp)).2.2 ⟨c, fun i => by ring⟩

end MathlibExtTest.Probability.Causality
