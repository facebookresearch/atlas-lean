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
open scoped unitInterval NNReal

namespace MathlibExtTest.Probability.Statistics.ExactTests.ConditionalBinomial

/-- Non-vacuity: the coordinates of `Po(r) ⊗ Po(r)` are independent Poisson counts with a
common rate, so the equal-rate Poisson null is satisfiable. -/
theorem witness (r : ℝ≥0) :
    HasLaw (fun ω : ℕ × ℕ => ω.1) (poissonMeasure r) ((poissonMeasure r).prod (poissonMeasure r)) ∧
      HasLaw (fun ω : ℕ × ℕ => ω.2) (poissonMeasure r)
        ((poissonMeasure r).prod (poissonMeasure r)) ∧
      IndepFun (fun ω : ℕ × ℕ => ω.1) (fun ω : ℕ × ℕ => ω.2)
        ((poissonMeasure r).prod (poissonMeasure r)) :=
  ⟨measurePreserving_fst.hasLaw, measurePreserving_snd.hasLaw,
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id⟩

/-- On the witness, the first count given the total `N` is `Bin(N, 1/2)`. -/
example (N : ℕ) :
    HasLaw (fun ω : ℕ × ℕ => ω.1) (binomial N ⟨1 / 2, by norm_num, by norm_num⟩)
      (((poissonMeasure 1).prod (poissonMeasure 1))[|{ω : ℕ × ℕ | ω.1 + ω.2 = N}]) :=
  hasLaw_cond_binomial_half one_pos measurable_fst measurable_snd (witness 1).1 (witness 1).2.1
    (witness 1).2.2 N

/-- McNemar's exact p-value is valid on the witness, given each number of discordant pairs and
unconditionally. -/
example :
    (∀ N, IsValidPValue (((poissonMeasure 1).prod (poissonMeasure 1))[|
        {ω : ℕ × ℕ | ω.1 + ω.2 = N}])
        (condBinomialTestPValue (fun ω : ℕ × ℕ => ω.1) (fun ω => ω.2))) ∧
      IsValidPValue ((poissonMeasure 1).prod (poissonMeasure 1))
        (condBinomialTestPValue (fun ω : ℕ × ℕ => ω.1) (fun ω => ω.2)) :=
  mcnemar_isValidPValue one_pos measurable_fst measurable_snd (witness 1).1 (witness 1).2.1
    (witness 1).2.2

/-- The TDT p-value is valid on the witness unconditionally. -/
example :
    IsValidPValue ((poissonMeasure 1).prod (poissonMeasure 1))
      (condBinomialTestPValue (fun ω : ℕ × ℕ => ω.1) (fun ω => ω.2)) :=
  (tdt_isValidPValue one_pos measurable_fst measurable_snd (witness 1).1 (witness 1).2.1
    (witness 1).2.2).2

/-- Boundary: observing `X = 0` gives p-value `1`. -/
example (N : ℕ) (p : I) : condBinomialPValue N p 0 = 1 := by
  simp [condBinomialPValue]

/-- Numeric value: one discordant pair, of type `(1, 0)`, gives the McNemar p-value
`P(Bin(1, 1/2) ≥ 1) = 1/2`. -/
example : condBinomialTestPValue (fun ω : ℕ × ℕ => ω.1) (fun ω => ω.2) (1, 0) = 1 / 2 := by
  have hset : {j : ℕ | 1 ≤ j} = {0}ᶜ := by
    ext j
    simp [Nat.one_le_iff_ne_zero]
  simp only [condBinomialTestPValue, condBinomialPValue, Nat.add_zero, hset]
  rw [measureReal_compl (measurableSet_singleton 0), binomial_real_singleton]
  norm_num

end MathlibExtTest.Probability.Statistics.ExactTests.ConditionalBinomial
