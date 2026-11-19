/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.ConditionalBinomial

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.ExactTests
  MathlibExt.Probability.Statistics.MultipleTesting
  MathlibExt.Biology.StatisticalGenetics.TransmissionTest
open scoped unitInterval NNReal

namespace MathlibExtTest.Probability.Statistics.ExactTests.ConditionalBinomial

/-- Fixed total as a special case, with totals of probability zero: under `Bin(3, 1/2)` with the
constant total `D = 3`, every total `d ≠ 3` has probability zero and imposes nothing, and the
random-total TDT p-value is valid. -/
example :
    IsValidPValue Bin(3, fairCoin) (fun k : ℕ => tdtPValue ((fun _ : ℕ => 3) k) id k) := by
  refine isValidPValue_tdtPValue_total_of_cond measurable_const fun d hd => ?_
  by_cases h3 : d = 3
  · subst h3
    simp
  · exact absurd (by simp [Ne.symm h3]) hd

/-- Totals of probability zero for McNemar: under `δ_(0,0)` (no discordant pairs) every total
`N ≠ 0` has probability zero, and the hypothesis on conditional laws still holds, so the
McNemar p-value at the observed total is valid. -/
example :
    IsValidPValue (Measure.dirac ((0, 0) : ℕ × ℕ))
      (fun ω : ℕ × ℕ => mcnemarPValue (ω.1 + ω.2) Prod.fst ω) := by
  refine isValidPValue_mcnemarPValue_total_of_cond measurable_fst measurable_snd fun N hN => ?_
  have hS : MeasurableSet {ω : ℕ × ℕ | ω.1 + ω.2 = N} := .of_discrete
  by_cases h0 : N = 0
  · subst h0
    have hcond : (Measure.dirac ((0, 0) : ℕ × ℕ))[|{ω : ℕ × ℕ | ω.1 + ω.2 = 0}] =
        Measure.dirac (0, 0) := by
      ext t ht
      rw [cond_apply hS, Measure.dirac_apply' _ hS, Measure.dirac_apply' _ (hS.inter ht),
        Measure.dirac_apply' _ ht]
      by_cases ht0 : ((0, 0) : ℕ × ℕ) ∈ t <;> simp [Set.indicator, ht0]
    rw [hcond, binomial_zero]
    exact ⟨measurable_fst.aemeasurable, Measure.map_dirac' measurable_fst _⟩
  · exact absurd (by simp [Measure.dirac_apply' _ hS, Ne.symm h0]) hN

/-- Non-vacuity of the Poisson null: the coordinates of `Po(r) ⊗ Po(r)` are independent Poisson
counts with a common rate. -/
theorem witness (r : ℝ≥0) :
    HasLaw (fun ω : ℕ × ℕ => ω.1) (poissonMeasure r) ((poissonMeasure r).prod (poissonMeasure r)) ∧
      HasLaw (fun ω : ℕ × ℕ => ω.2) (poissonMeasure r)
        ((poissonMeasure r).prod (poissonMeasure r)) ∧
      IndepFun (fun ω : ℕ × ℕ => ω.1) (fun ω : ℕ × ℕ => ω.2)
        ((poissonMeasure r).prod (poissonMeasure r)) :=
  ⟨measurePreserving_fst.hasLaw, measurePreserving_snd.hasLaw,
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id⟩

/-- McNemar's p-value at the observed number of discordant pairs is valid on the witness, for
every common rate, including `r = 0`. -/
example (r : ℝ≥0) :
    IsValidPValue ((poissonMeasure r).prod (poissonMeasure r))
      (fun ω : ℕ × ℕ => mcnemarPValue (ω.1 + ω.2) Prod.fst ω) :=
  isValidPValue_mcnemarPValue_total measurable_fst measurable_snd (witness r).1 (witness r).2.1
    (witness r).2.2

end MathlibExtTest.Probability.Statistics.ExactTests.ConditionalBinomial
