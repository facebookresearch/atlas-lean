/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.UniversalInference

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.MultipleTesting
  MathlibExt.Probability.Statistics.MultipleTesting.UniversalInference
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.UniversalInference

/-! ### A composite Bernoulli null on a three-point grid

Parameters `θ ∈ {1/4, 1/2, 3/4}` (indices `0, 1, 2`); one Bernoulli observation in each split.
Null `Θ₀ = {1/4, 1/2}`. The estimator on `D₁` is the unrestricted MLE (`3/4` after `true`,
`1/4` after `false`); the null MLE on `D₀` is `1/2` after `true` and `1/4` after `false`.

The split LRT `T(x₀, x₁)` takes the values `3/2, 1/2, 1/3, 1` at
`(true, true), (true, false), (false, true), (false, false)`. Every expectation below is
computed from the definitions, not through the theorems under test:

* under the null parameters `1/2` and `1/4`, `E[T] = 5/6` and `13/16`, both at most `1`;
* under the alternative `3/4`, `E[T] = 17/16 > 1`, so `T` is not an e-value there and the
  hypothesis `θ⋆ ∈ Θ₀` is needed;
* the same ratio computed *without splitting* (estimate fitted on `D₀` itself) has null
  expectation `5/4 > 1`, so the split is needed. -/

/-- The parameter grid. -/
noncomputable def par : Fin 3 → ℝ := ![1 / 4, 1 / 2, 3 / 4]

/-- Bernoulli likelihood of one observation. -/
noncomputable def bern (θ : Fin 3) (b : Bool) : ℝ := if b then par θ else 1 - par θ

/-- Counting measure on `Bool`. -/
noncomputable def ref : Measure Bool := Measure.dirac true + Measure.dirac false

/-- The composite null `{1/4, 1/2}`. -/
def nullSet : Set (Fin 3) := {0, 1}

/-- Estimator fitted on `D₁`: the unrestricted MLE over the grid. -/
def thetaHat1 (b : Bool) : Fin 3 := if b then 2 else 0

/-- Null MLE on `D₀`. -/
def thetaHat0 (b : Bool) : Fin 3 := if b then 1 else 0

/-- The joint law of `(D₀, D₁)`: `D₀ ~ Bern(par a)` and `D₁ ~ Bern(par b)`, independent. -/
noncomputable def P (a b : Fin 3) : Measure (Bool × Bool) :=
  (lawOf ref bern a).prod (lawOf ref bern b)

/-- The split LRT of the example. -/
noncomputable def T : Bool × Bool → ℝ := splitLRT bern thetaHat1 thetaHat0

theorem bern_nonneg (θ : Fin 3) (b : Bool) : 0 ≤ bern θ b := by
  fin_cases θ <;> cases b <;> norm_num [bern, par]

theorem lintegral_ref (f : Bool → ENNReal) : ∫⁻ b, f b ∂ref = f true + f false := by
  simp [ref, lintegral_add_measure, lintegral_dirac]

theorem lintegral_bern (θ : Fin 3) : ∫⁻ b, ENNReal.ofReal (bern θ b) ∂ref = 1 := by
  rw [lintegral_ref, ← ENNReal.ofReal_add (bern_nonneg _ _) (bern_nonneg _ _)]
  simp [bern]

theorem isNullMLE : IsNullMLE bern nullSet thetaHat0 where
  mem b := by cases b <;> simp [nullSet, thetaHat0]
  le_max b θ hθ := by
    rcases hθ with rfl | rfl <;> cases b <;> norm_num [bern, par, thetaHat0]

theorem one_mem_nullSet : (1 : Fin 3) ∈ nullSet := by simp [nullSet]

theorem zero_mem_nullSet : (0 : Fin 3) ∈ nullSet := by simp [nullSet]

theorem two_not_mem_nullSet : (2 : Fin 3) ∉ nullSet := by simp [nullSet]

instance (θ : Fin 3) : IsProbabilityMeasure (lawOf ref bern θ) := by
  constructor
  rw [lawOf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_bern]

theorem T_values :
    T (true, true) = 3 / 2 ∧ T (true, false) = 1 / 2 ∧ T (false, true) = 1 / 3 ∧
      T (false, false) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [T, splitLRT, splitLR, thetaHat1, thetaHat0, bern, par]

theorem T_nonneg (z : Bool × Bool) : 0 ≤ T z := by
  obtain ⟨h1, h2, h3, h4⟩ := T_values
  rcases z with ⟨_ | _, _ | _⟩ <;> norm_num [h1, h2, h3, h4]

/-! ### Integrals over the finite model, from the definitions -/

theorem lintegral_lawOf (θ : Fin 3) (g : Bool → ENNReal) :
    ∫⁻ b, g b ∂lawOf ref bern θ =
      ENNReal.ofReal (bern θ true) * g true + ENNReal.ofReal (bern θ false) * g false := by
  rw [lawOf, lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
    (measurable_of_countable _), lintegral_ref]
  rfl

theorem lintegral_P (a b : Fin 3) (f : Bool × Bool → ENNReal) :
    ∫⁻ z, f z ∂P a b =
      ENNReal.ofReal (bern a true) * ENNReal.ofReal (bern b true) * f (true, true) +
        ENNReal.ofReal (bern a true) * ENNReal.ofReal (bern b false) * f (true, false) +
        ENNReal.ofReal (bern a false) * ENNReal.ofReal (bern b true) * f (false, true) +
        ENNReal.ofReal (bern a false) * ENNReal.ofReal (bern b false) * f (false, false) := by
  rw [P, lintegral_prod _ (measurable_of_countable f).aemeasurable]
  simp only [lintegral_lawOf]
  ring

theorem lintegral_P_ofReal (a b : Fin 3) (g : Bool × Bool → ℝ) (hg : ∀ z, 0 ≤ g z) :
    ∫⁻ z, ENNReal.ofReal (g z) ∂P a b =
      ENNReal.ofReal (bern a true * bern b true * g (true, true) +
        bern a true * bern b false * g (true, false) +
        bern a false * bern b true * g (false, true) +
        bern a false * bern b false * g (false, false)) := by
  have n : ∀ x y, 0 ≤ bern a x * bern b y * g (x, y) := fun x y =>
    mul_nonneg (mul_nonneg (bern_nonneg _ _) (bern_nonneg _ _)) (hg _)
  have e : ∀ x y, ENNReal.ofReal (bern a x) * ENNReal.ofReal (bern b y) *
      ENNReal.ofReal (g (x, y)) = ENNReal.ofReal (bern a x * bern b y * g (x, y)) := fun x y => by
    rw [ENNReal.ofReal_mul (mul_nonneg (bern_nonneg _ _) (bern_nonneg _ _)),
      ENNReal.ofReal_mul (bern_nonneg _ _)]
  rw [lintegral_P, e, e, e, e, ← ENNReal.ofReal_add (n _ _) (n _ _),
    ← ENNReal.ofReal_add (add_nonneg (n _ _) (n _ _)) (n _ _),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (n _ _) (n _ _)) (n _ _)) (n _ _)]

/-- Computed from the definitions: under the null parameter `1/2`, `E[T] = 5/6`. -/
theorem lintegral_T_half : ∫⁻ z, ENNReal.ofReal (T z) ∂P 1 1 = ENNReal.ofReal (5 / 6) := by
  obtain ⟨h1, h2, h3, h4⟩ := T_values
  rw [lintegral_P_ofReal _ _ _ T_nonneg, h1, h2, h3, h4]
  norm_num [bern, par]

/-- Computed from the definitions: under the null parameter `1/4`, `E[T] = 13/16`. -/
theorem lintegral_T_quarter :
    ∫⁻ z, ENNReal.ofReal (T z) ∂P 0 0 = ENNReal.ofReal (13 / 16) := by
  obtain ⟨h1, h2, h3, h4⟩ := T_values
  rw [lintegral_P_ofReal _ _ _ T_nonneg, h1, h2, h3, h4]
  norm_num [bern, par]

/-- Computed from the definitions: under the alternative `3/4`, `E[T] = 17/16 > 1`. -/
theorem lintegral_T_alt :
    ∫⁻ z, ENNReal.ofReal (T z) ∂P 2 2 = ENNReal.ofReal (17 / 16) := by
  obtain ⟨h1, h2, h3, h4⟩ := T_values
  rw [lintegral_P_ofReal _ _ _ T_nonneg, h1, h2, h3, h4]
  norm_num [bern, par]

/-- Off the null the split LRT is not an e-value: the hypothesis `θ⋆ ∈ Θ₀` is needed. -/
theorem not_isEValue_T_alt : ¬ IsEValue (P 2 2) T := by
  intro h
  have h1 := h.lintegral_le_one
  rw [lintegral_T_alt, ENNReal.ofReal_le_one] at h1
  norm_num at h1

/-! ### Without splitting the ratio is not an e-value

The same ratio with the estimate fitted on `D₀` itself, `p_{θ̂(D₀)}(D₀) / p_{θ̂₀(D₀)}(D₀)`, is
the classical likelihood-ratio statistic. It takes the values `3/2` and `1`, and its expectation
under the null parameter `1/2` is `5/4`. -/

/-- The unsplit likelihood ratio. -/
noncomputable def naiveLR (b : Bool) : ℝ := bern (thetaHat1 b) b / bern (thetaHat0 b) b

theorem lintegral_naiveLR :
    ∫⁻ b, ENNReal.ofReal (naiveLR b) ∂lawOf ref bern 1 = ENNReal.ofReal (5 / 4) := by
  rw [lintegral_lawOf, ← ENNReal.ofReal_mul (bern_nonneg _ _),
    ← ENNReal.ofReal_mul (bern_nonneg _ _), ← ENNReal.ofReal_add]
  · norm_num [naiveLR, bern, par, thetaHat1, thetaHat0]
  · exact mul_nonneg (bern_nonneg _ _) (by norm_num [naiveLR, bern, par, thetaHat1, thetaHat0])
  · exact mul_nonneg (bern_nonneg _ _) (by norm_num [naiveLR, bern, par, thetaHat1, thetaHat0])

theorem not_isEValue_naiveLR : ¬ IsEValue (lawOf ref bern 1) naiveLR := by
  intro h
  have h1 := h.lintegral_le_one
  rw [lintegral_naiveLR, ENNReal.ofReal_le_one] at h1
  norm_num at h1

/-! ### The theorems apply to the example -/

theorem measurable_T : Measurable T := measurable_of_countable _

/-- The split LRT is an e-value under the null parameter `1/2`. -/
theorem isEValue_T_half : IsEValue (P 1 1) T :=
  isEValue_splitLRT bern_nonneg (fun θ => (lintegral_bern θ).le) isNullMLE one_mem_nullSet
    (measurable_of_countable _) measurable_T

/-- The split LRT is an e-value under the null parameter `1/4`. -/
theorem isEValue_T_quarter : IsEValue (P 0 0) T :=
  isEValue_splitLRT bern_nonneg (fun θ => (lintegral_bern θ).le) isNullMLE zero_mem_nullSet
    (measurable_of_countable _) measurable_T

/-- Consistency with the direct computation: `5/6 ≤ 1` and `13/16 ≤ 1`. -/
example : ENNReal.ofReal (5 / 6) ≤ 1 ∧ ENNReal.ofReal (13 / 16) ≤ 1 :=
  ⟨by rw [← lintegral_T_half]; exact isEValue_T_half.lintegral_le_one,
    by rw [← lintegral_T_quarter]; exact isEValue_T_quarter.lintegral_le_one⟩

/-! ### Rejection regions at `α = 2/3` and `α = 3/4`

At `α = 2/3`, `1 / α = 3/2 = T(true, true)`: the split LRT (`T > 1 / α`) rejects nowhere, while
the boundary-inclusive variant (`T ≥ 1 / α`) rejects exactly at `(true, true)`. At `α = 3/4`,
`1 / α = 4/3`, and the split LRT rejects exactly at `(true, true)`. That point has null
probability `1/4` under `1/2`, computed from the definitions; the theorems bound it by `α`. -/

/-- The split LRT does not reject on the boundary `T = 1 / α`. -/
theorem splitLRTRejects_two_thirds :
    splitLRTRejects bern thetaHat1 thetaHat0 (2 / 3) = ∅ := by
  ext z
  rcases z with ⟨_ | _, _ | _⟩ <;>
    norm_num [splitLRTRejects, bern, par, thetaHat1, thetaHat0]

theorem splitLRTRejects_three_quarters :
    splitLRTRejects bern thetaHat1 thetaHat0 (3 / 4) = {(true, true)} := by
  ext z
  rcases z with ⟨_ | _, _ | _⟩ <;>
    norm_num [splitLRTRejects, bern, par, thetaHat1, thetaHat0]

/-- On the example, where every likelihood is positive, the rejection region is
`α⁻¹ < T`. -/
example (z : Bool × Bool) :
    z ∈ splitLRTRejects bern thetaHat1 thetaHat0 (3 / 4) ↔ (3 / 4 : ℝ)⁻¹ < T z :=
  mem_splitLRTRejects_iff (by norm_num) (by
    rcases z with ⟨_ | _, _ | _⟩ <;> norm_num [bern, par, thetaHat0])

theorem splitLRTRejectsClosed_eq :
    splitLRTRejectsClosed bern thetaHat1 thetaHat0 (2 / 3) = {(true, true)} := by
  obtain ⟨h1, h2, h3, h4⟩ := T_values
  ext z
  change (2 / 3 : ℝ)⁻¹ ≤ T z ↔ z = (true, true)
  rcases z with ⟨_ | _, _ | _⟩ <;> simp only [h1, h2, h3, h4] <;> norm_num

theorem P_true_true : P 1 1 {(true, true)} = ENNReal.ofReal (1 / 4) := by
  rw [← lintegral_indicator_one (measurableSet_singleton _), lintegral_P]
  simp only [Set.indicator, Set.mem_singleton_iff, Prod.mk.injEq, Pi.one_apply]
  norm_num [bern, par]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem P_splitLRTRejects :
    P 1 1 (splitLRTRejects bern thetaHat1 thetaHat0 (3 / 4)) = ENNReal.ofReal (1 / 4) := by
  rw [splitLRTRejects_three_quarters, P_true_true]

theorem P_splitLRTRejectsClosed :
    P 1 1 (splitLRTRejectsClosed bern thetaHat1 thetaHat0 (2 / 3)) = ENNReal.ofReal (1 / 4) := by
  rw [splitLRTRejectsClosed_eq, P_true_true]

example : P 1 1 (splitLRTRejects bern thetaHat1 thetaHat0 (3 / 4)) ≤ ENNReal.ofReal (3 / 4) :=
  measure_splitLRTRejects_le bern_nonneg (fun θ => (lintegral_bern θ).le) isNullMLE
    one_mem_nullSet (measurable_of_countable _) measurable_T (by norm_num)

example :
    P 1 1 (splitLRTRejectsClosed bern thetaHat1 thetaHat0 (2 / 3)) ≤ ENNReal.ofReal (2 / 3) :=
  measure_splitLRTRejectsClosed_le bern_nonneg (fun θ => (lintegral_bern θ).le) isNullMLE
    one_mem_nullSet (measurable_of_countable _) measurable_T (by norm_num)

example : ENNReal.ofReal (1 / 4) ≤ ENNReal.ofReal (2 / 3) :=
  ENNReal.ofReal_le_ofReal (by norm_num)

/-- The split-LRT p-value is valid under the null parameter `1/2`. -/
example : IsValidPValue (P 1 1) fun z => (max (T z) 1)⁻¹ :=
  isValidPValue_splitLRT bern_nonneg (fun θ => (lintegral_bern θ).le) isNullMLE
    one_mem_nullSet (measurable_of_countable _) measurable_T

/-! ### Universal confidence sets

At `α = 2/3` and `(D₀, D₁) = (true, true)`, the parameter `1/2` has `Tₙ = (3/4) / (1/2) = 3/2`,
exactly `1 / α`: it lies in the universal confidence set (`Tₙ ≤ 1 / α`) but not in the strict
variant (`Tₙ < 1 / α`). -/

example : (1 : Fin 3) ∈ universalConfidenceSet bern thetaHat1 (2 / 3) (true, true) := by
  norm_num [universalConfidenceSet, bern, par, thetaHat1]

example : (1 : Fin 3) ∉ universalConfidenceSetStrict bern thetaHat1 (2 / 3) (true, true) := by
  norm_num [universalConfidenceSetStrict, splitLR, bern, par, thetaHat1]

/-- Coverage of the universal confidence set at the true parameter `3/4`. -/
example : P 2 2 {z | (2 : Fin 3) ∉ universalConfidenceSet bern thetaHat1 (1 / 2) z} ≤
    ENNReal.ofReal (1 / 2) :=
  measure_not_mem_universalConfidenceSet_le bern_nonneg (fun θ => (lintegral_bern θ).le)
    (measurable_of_countable _) (measurable_of_countable _) (by norm_num)

/-- Coverage of the strict variant at the true parameter `3/4`. -/
example : P 2 2 {z | (2 : Fin 3) ∉ universalConfidenceSetStrict bern thetaHat1 (1 / 2) z} ≤
    ENNReal.ofReal (1 / 2) :=
  measure_not_mem_universalConfidenceSetStrict_le bern_nonneg (fun θ => (lintegral_bern θ).le)
    (measurable_of_countable _) (measurable_of_countable _) (by norm_num)

end MathlibExtTest.Probability.Statistics.MultipleTesting.UniversalInference
