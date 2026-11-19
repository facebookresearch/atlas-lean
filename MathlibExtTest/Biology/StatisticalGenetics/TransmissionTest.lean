/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.TransmissionTest
public import MathlibExt.Probability.Statistics.MultipleTesting.Bonferroni

/-! # Tests for `MathlibExt.Biology.StatisticalGenetics.TransmissionTest`

The numeric tails for `d = 4` are computed from the binomial point masses
(`binomial_eq_sum_dirac`), not from `upperTail_binomial_fairCoin`; that theorem is checked
against them separately. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset MathlibExt.Probability.Statistics.ExactTests
open MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Biology.StatisticalGenetics.TransmissionTest
open scoped unitInterval NNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.TransmissionTest

/-- `fairCoin` is the real number `1/2`. -/
example : (fairCoin : ℝ) = 1 / 2 := coe_fairCoin

/-- Boundary `d = 0`: with no informative transmissions the only possible count is `0`, and its
TDT p-value is `1`. -/
example {Ω : Type*} (B : Ω → ℕ) (ω : Ω) (h : B ω = 0) : tdtPValue 0 B ω = 1 := by
  simp [tdtPValue, upperTailPValue, upperTail, h]

/-- Boundary `k = 0`: an observed count of `0` has TDT p-value `1`, for every `d`. -/
example {Ω : Type*} (d : ℕ) (B : Ω → ℕ) (ω : Ω) (h : B ω = 0) : tdtPValue d B ω = 1 := by
  simp [tdtPValue, upperTailPValue, upperTail, h]

/-- The upper tail of `Bin(4, 1/2)`, summed over its point masses `C(4, j) / 16`. -/
private lemma upperTail_four_fairCoin_eq (k : ℕ) :
    upperTail Bin(4, fairCoin) k =
      ∑ j ∈ ({0, 1, 2, 3, 4} : Finset ℕ), if k ≤ j then (4 : ℕ).choose j / (16 : ℝ) else 0 := by
  rw [upperTail, binomial_eq_sum_dirac, measureReal_def, Measure.coe_finsetSum, Finset.sum_apply,
    show Iic 4 = ({0, 1, 2, 3, 4} : Finset ℕ) by decide]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (.of_discrete)]
  rw [ENNReal.toReal_sum fun j _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (by unfold Set.indicator; split_ifs <;> simp)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj4 : j ≤ 4 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hj; omega
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal binomial_nonneg, coe_fairCoin,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  by_cases hk : k ≤ j <;> simp only [Set.indicator, Set.mem_ofPred_eq, hk, ite_true, ite_false] <;>
    interval_cases j <;> norm_num [Nat.choose]

/-- `d = 4`, observed `4`: the TDT p-value is `P(Bin(4, 1/2) = 4) = 1/16`. -/
example : upperTail Bin(4, fairCoin) 4 = 1 / 16 := by
  rw [upperTail_four_fairCoin_eq]
  norm_num [Finset.sum_insert, Nat.choose]

/-- `d = 4`, observed `3`: `P(Bin(4, 1/2) ≥ 3) = (4 + 1) / 16 = 5/16`. -/
example : upperTail Bin(4, fairCoin) 3 = 5 / 16 := by
  rw [upperTail_four_fairCoin_eq]
  norm_num [Finset.sum_insert, Nat.choose]

/-- The closed form agrees with the point-mass values: `(C(4,3) + C(4,4)) / 2^4 = 5/16`. -/
example : upperTail Bin(4, fairCoin) 3 = 5 / 16 := by
  rw [upperTail_binomial_fairCoin, show Icc 3 4 = ({3, 4} : Finset ℕ) by decide]
  norm_num [Nat.choose]

/-- The TDT p-value at the observed count `4` among `d = 4`. -/
example {Ω : Type*} (B : Ω → ℕ) (ω : Ω) (h : B ω = 4) : tdtPValue 4 B ω = 1 / 16 := by
  rw [tdtPValue, upperTailPValue, h, upperTail_binomial_fairCoin]
  norm_num

/-- Non-vacuity of the TDT: the identity on `ℕ` under `Bin(d, 1/2)` meets the null hypothesis. -/
example (d : ℕ) : IsValidPValue Bin(d, fairCoin) (tdtPValue d id) :=
  isValidPValue_tdtPValue HasLaw.id

/-- Non-vacuity of the McNemar theorem on the canonical space `Po(a) ⊗ Po(a)` of two
independent Poisson counts with equal rate. -/
example (a : ℝ≥0) (ha : 0 < a) (N : ℕ) :
    IsValidPValue (((poissonMeasure a).prod (poissonMeasure a))[|{ω : ℕ × ℕ | ω.1 + ω.2 = N}])
      (mcnemarPValue N Prod.fst) :=
  isValidPValue_mcnemarPValue ha measurable_fst measurable_snd measurePreserving_fst.hasLaw
    measurePreserving_snd.hasLaw (indepFun_prod (X := id) (Y := id) measurable_id measurable_id) N

/-- On `Po(1) ⊗ Po(1)`, the first count given `X + Y = N` is `Bin(N, 1/2)`. -/
example (N : ℕ) :
    HasLaw Prod.fst Bin(N, fairCoin)
      (((poissonMeasure 1).prod (poissonMeasure 1))[|{ω : ℕ × ℕ | ω.1 + ω.2 = N}]) :=
  hasLaw_cond_binomial_fairCoin one_pos measurable_fst measurable_snd
    measurePreserving_fst.hasLaw measurePreserving_snd.hasLaw
    (indepFun_prod (X := id) (Y := id) measurable_id measurable_id) N

/-- The McNemar and TDT p-values are the same binomial tail. -/
example {Ω : Type*} (N : ℕ) (X : Ω → ℕ) : mcnemarPValue N X = tdtPValue N X := rfl

/-- Two TDT p-values (two markers, each with a fair-coin null) feed the Bonferroni FWER bound
directly through their `IsValidPValue` type. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d₁ d₂ : ℕ} {B₁ B₂ : Ω → ℕ}
    (h₁ : HasLaw B₁ Bin(d₁, fairCoin) μ) (h₂ : HasLaw B₂ Bin(d₂, fairCoin) μ) {α : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    μ {ω | (bonferroniRejections α (fun i => ![tdtPValue d₁ B₁, tdtPValue d₂ B₂] i ω) ∩
      univ).Nonempty} ≤ ENNReal.ofReal α :=
  measure_bonferroni_familywiseError_le μ ![tdtPValue d₁ B₁, tdtPValue d₂ B₂] univ
    (fun i _ => by fin_cases i
                   · exact isValidPValue_tdtPValue h₁
                   · exact isValidPValue_tdtPValue h₂) hα₀ hα₁

end MathlibExtTest.Biology.StatisticalGenetics.TransmissionTest
