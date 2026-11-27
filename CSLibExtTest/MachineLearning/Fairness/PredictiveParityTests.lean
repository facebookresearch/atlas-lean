/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Fairness.PredictiveParity

@[expose] public section

/-!
# Tests for predictive parity versus error-rate balance

Small groups given by the four cell masses of the joint law of `(Y, Ŷ)`: the identity on a
concrete group, two groups with equal positive predictive values and equal false-negative rates
whose false-positive rates differ in the ratio of their prevalence odds, the boundary cases that
the hypotheses exclude, the two exceptions at different prevalences, and the identity for random
variables on an arbitrary probability space.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Cslib.MachineLearning.Fairness
open scoped ENNReal NNReal

namespace CSLibExtTest.MachineLearning.Fairness.PredictiveParity

/-- The measure with masses `a`, `b`, `c`, `d` at `(true, true)` (true positives),
`(false, true)` (false positives), `(true, false)` (false negatives) and `(false, false)` (true
negatives). -/
noncomputable def group (a b c d : ℝ≥0) : Measure (Bool × Bool) :=
  a • Measure.dirac (true, true) + b • Measure.dirac (false, true) +
    c • Measure.dirac (true, false) + d • Measure.dirac (false, false)

instance (a b c d : ℝ≥0) : IsFiniteMeasure (group a b c d) := by
  unfold group; infer_instance

theorem group_real (a b c d : ℝ≥0) :
    (group a b c d).real {(true, true)} = a ∧ (group a b c d).real {(false, true)} = b ∧
      (group a b c d).real {(true, false)} = c ∧ (group a b c d).real {(false, false)} = d := by
  simp [group, measureReal_def]

theorem isProbabilityMeasure_group {a b c d : ℝ≥0} (h : a + b + c + d = 1) :
    IsProbabilityMeasure (group a b c d) := by
  constructor
  simp only [group, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
  exact_mod_cast h

/-! ### A group and the identity -/

/-- Prevalence `2/5`, `PPV = 3/4`, `FNR = 1/4` and `FPR = 1/6`. -/
noncomputable abbrev groupA : Measure (Bool × Bool) := group (3 / 10) (1 / 10) (1 / 10) (1 / 2)

instance : IsProbabilityMeasure groupA :=
  isProbabilityMeasure_group (by norm_num)

theorem groupA_rates :
    prevalence groupA = 2 / 5 ∧ positivePredictiveValue groupA = 3 / 4 ∧
      falseNegativeRate groupA = 1 / 4 ∧ falsePositiveRate groupA = 1 / 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := group_real (3 / 10) (1 / 10) (1 / 10) (1 / 2)
  rw [prevalence_eq, positivePredictiveValue_eq, falseNegativeRate_eq, falsePositiveRate_eq,
    h1, h2, h3, h4]
  norm_num

/-- The identity on `groupA`: `1/6 = (2/3) * (1/3) * (3/4)`. -/
example :
    falsePositiveRate groupA = prevalence groupA / (1 - prevalence groupA) *
      ((1 - positivePredictiveValue groupA) / positivePredictiveValue groupA) *
        (1 - falseNegativeRate groupA) := by
  obtain ⟨hp, hv, hf, hr⟩ := groupA_rates
  rw [hp, hv, hf, hr]
  norm_num

/-! ### Equal PPV and FNR, different prevalences -/

/-- Prevalence `1/2` with the same `PPV = 3/4` and `FNR = 1/4` as `groupA`, so `FPR = 1/4`. -/
noncomputable abbrev groupB : Measure (Bool × Bool) := group (3 / 8) (1 / 8) (1 / 8) (3 / 8)

instance : IsProbabilityMeasure groupB :=
  isProbabilityMeasure_group (by norm_num)

theorem groupB_rates :
    prevalence groupB = 1 / 2 ∧ positivePredictiveValue groupB = 3 / 4 ∧
      falseNegativeRate groupB = 1 / 4 ∧ falsePositiveRate groupB = 1 / 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := group_real (3 / 8) (1 / 8) (1 / 8) (3 / 8)
  rw [prevalence_eq, positivePredictiveValue_eq, falseNegativeRate_eq, falsePositiveRate_eq,
    h1, h2, h3, h4]
  norm_num

/-- Predictive parity and equal false-negative rates, but unequal false-positive rates, as the
trade-off requires: neither exception holds. -/
example : falsePositiveRate groupA ≠ falsePositiveRate groupB := by
  intro h
  have hpos : ∀ μ : Measure (Bool × Bool), μ = groupA ∨ μ = groupB →
      0 < μ.real {z | z.2 = true} := by
    rintro μ (rfl | rfl) <;>
    · rw [measureReal_snd_eq_true, (group_real _ _ _ _).1, (group_real _ _ _ _).2.1]
      norm_num
  obtain ⟨hpA, hvA, hfA, -⟩ := groupA_rates
  obtain ⟨hpB, hvB, hfB, -⟩ := groupB_rates
  rcases predictiveParity_errorRateBalance_tradeoff.2.1 groupA groupB
      (by rw [hpA]; norm_num) (by rw [hpA]; norm_num) (hpos _ (Or.inl rfl))
      (by rw [hpB]; norm_num) (by rw [hpB]; norm_num) (hpos _ (Or.inr rfl))
      (by rw [hvA, hvB]) (by rw [hpA, hpB]; norm_num) h (by rw [hfA, hfB]) with
    ⟨hf, -⟩ | ⟨hv, -⟩
  · rw [hfA] at hf; norm_num at hf
  · rw [hvA] at hv; norm_num at hv

/-! ### Boundary cases -/

/-- Without `PPV > 0` the identity fails: here `PPV = 0` (so `FNR = 1`) and `FPR = 1/2`, while
the right-hand side is `0` because `x / 0 = 0`. -/
example :
    falsePositiveRate (group 0 (1 / 4) (1 / 2) (1 / 4)) ≠
      prevalence (group 0 (1 / 4) (1 / 2) (1 / 4)) /
        (1 - prevalence (group 0 (1 / 4) (1 / 2) (1 / 4))) *
        ((1 - positivePredictiveValue (group 0 (1 / 4) (1 / 2) (1 / 4))) /
          positivePredictiveValue (group 0 (1 / 4) (1 / 2) (1 / 4))) *
        (1 - falseNegativeRate (group 0 (1 / 4) (1 / 2) (1 / 4))) := by
  obtain ⟨h1, h2, h3, h4⟩ := group_real 0 (1 / 4) (1 / 2) (1 / 4)
  rw [prevalence_eq, positivePredictiveValue_eq, falseNegativeRate_eq, falsePositiveRate_eq,
    h1, h2, h3, h4]
  norm_num

/-- With prevalence `0` the conditioning event of `FNR` is null, so `FNR = 0` while `PPV = 0`:
the equivalence of `FNR = 1` and `PPV = 0` needs `p > 0`. -/
example :
    prevalence (group 0 (1 / 2) 0 (1 / 2)) = 0 ∧
      falseNegativeRate (group 0 (1 / 2) 0 (1 / 2)) = 0 ∧
        positivePredictiveValue (group 0 (1 / 2) 0 (1 / 2)) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := group_real 0 (1 / 2) 0 (1 / 2)
  rw [prevalence_eq, positivePredictiveValue_eq, falseNegativeRate_eq, h1, h2, h3]
  norm_num

/-- With no predicted positive the conditioning event of `PPV` is null and `PPV = 0`. -/
example :
    (group 0 0 (1 / 2) (1 / 2)).real {z | z.2 = true} = 0 ∧
      positivePredictiveValue (group 0 0 (1 / 2) (1 / 2)) = 0 ∧
        falseNegativeRate (group 0 0 (1 / 2) (1 / 2)) = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := group_real 0 0 (1 / 2) (1 / 2)
  rw [measureReal_snd_eq_true, positivePredictiveValue_eq, falseNegativeRate_eq, h1, h2, h3]
  norm_num

/-! ### Both exceptions occur at different prevalences -/

/-- Two groups of prevalences `1/4` and `1/2` with `PPV = 1` share `FPR = 0` and `FNR = 1/3`. -/
example : ∃ μ ν : Measure (Bool × Bool), IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
    prevalence μ ≠ prevalence ν ∧ positivePredictiveValue μ = positivePredictiveValue ν ∧
      falsePositiveRate μ = falsePositiveRate ν ∧ falseNegativeRate μ = falseNegativeRate ν := by
  obtain ⟨μ, hμ, hpμ, -, hvμ, hfμ, hrμ⟩ := predictiveParity_errorRateBalance_tradeoff.2.2.2.2.1
    (1 / 4) (by norm_num) (1 / 3) (by norm_num)
  obtain ⟨ν, hν, hpν, -, hvν, hfν, hrν⟩ := predictiveParity_errorRateBalance_tradeoff.2.2.2.2.1
    (1 / 2) (by norm_num) (1 / 3) (by norm_num)
  exact ⟨μ, ν, hμ, hν, by rw [hpμ, hpν]; norm_num, hvμ.trans hvν.symm, hrμ.trans hrν.symm,
    hfμ.trans hfν.symm⟩

/-- Two groups of prevalences `1/4` and `1/2` with `PPV = 0` share `FNR = 1` and `FPR = 1/2`. -/
example : ∃ μ ν : Measure (Bool × Bool), IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
    prevalence μ ≠ prevalence ν ∧ positivePredictiveValue μ = positivePredictiveValue ν ∧
      falsePositiveRate μ = falsePositiveRate ν ∧ falseNegativeRate μ = falseNegativeRate ν := by
  obtain ⟨μ, hμ, hpμ, -, hvμ, hfμ, hrμ⟩ := predictiveParity_errorRateBalance_tradeoff.2.2.2.2.2
    (1 / 4) (by norm_num) (1 / 2) (by norm_num)
  obtain ⟨ν, hν, hpν, -, hvν, hfν, hrν⟩ := predictiveParity_errorRateBalance_tradeoff.2.2.2.2.2
    (1 / 2) (by norm_num) (1 / 2) (by norm_num)
  exact ⟨μ, ν, hμ, hν, by rw [hpμ, hpν]; norm_num, hvμ.trans hvν.symm, hrμ.trans hrν.symm,
    hfμ.trans hfν.symm⟩

/-! ### Measures that are not probability measures -/

/-- The definitions take any measure: for twice the Dirac mass at `(true, true)`, `prevalence` is
the mass `2`. -/
example : prevalence ((2 : ℝ≥0∞) • Measure.dirac ((true, true) : Bool × Bool)) = 2 := by
  simp [prevalence, measureReal_def]

/-- An infinite conditioning mass gives the zero conditional measure, so the rate is `0`. -/
example : falsePositiveRate (∞ • Measure.dirac ((false, true) : Bool × Bool)) = 0 := by
  simp [falsePositiveRate, ProbabilityTheory.cond]

/-! ### Random variables on a probability space -/

/-- The identity for a label `Y` and a prediction `Ŷ` on an arbitrary probability space, with the
rates written as conditional probabilities there. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y Yhat : Ω → Bool} (hY : Measurable Y) (hYhat : Measurable Yhat)
    (hp₀ : 0 < P.real {ω | Y ω = true}) (hp₁ : P.real {ω | Y ω = true} < 1)
    (hppv : 0 < (P[|{ω | Yhat ω = true}]).real {ω | Y ω = true}) :
    (P[|{ω | Y ω = false}]).real {ω | Yhat ω = true} =
      P.real {ω | Y ω = true} / (1 - P.real {ω | Y ω = true}) *
        ((1 - (P[|{ω | Yhat ω = true}]).real {ω | Y ω = true}) /
          (P[|{ω | Yhat ω = true}]).real {ω | Y ω = true}) *
        (1 - (P[|{ω | Y ω = true}]).real {ω | Yhat ω = false}) := by
  have h := falsePositiveRate_eq_mul (P.map fun ω ↦ (Y ω, Yhat ω))
    (by rwa [prevalence_map P hY hYhat]) (by rwa [prevalence_map P hY hYhat])
    (by rwa [positivePredictiveValue_map P hY hYhat])
  rwa [falsePositiveRate_map P hY hYhat, prevalence_map P hY hYhat,
    positivePredictiveValue_map P hY hYhat, falseNegativeRate_map P hY hYhat] at h

end CSLibExtTest.MachineLearning.Fairness.PredictiveParity
