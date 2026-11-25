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
open scoped unitInterval

namespace MathlibExtTest.Probability.Statistics.ExactTests.ConditionalBinomial

/-- For a fixed total, only the realized value of the total has positive probability.
The success probability need not be `1/2`. -/
example (p : I) : IsValidPValue Bin(3, p) (fun k : ℕ => upperTailPValue Bin(3, p) id k) := by
  refine isValidPValue_binomialUpperTail_total_of_cond (D := fun _ => 3) measurable_const
    fun d hd => ?_
  by_cases h3 : d = 3
  · subst h3
    simp
  · exact absurd (by simp [Ne.symm h3]) hd

end MathlibExtTest.Probability.Statistics.ExactTests.ConditionalBinomial
