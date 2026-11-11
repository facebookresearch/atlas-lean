/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.TailPValue
public import MathlibExt.Probability.Distributions.Hypergeometric
public import Mathlib.Probability.Distributions.Binomial

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.ExactTests
open MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.ExactTests.TailPValue

/-- Non-vacuity: the identity on `ℕ` under the hypergeometric law `H(5, 2, 2)` has that law, so
its upper-tail p-value is valid. -/
example : IsValidPValue (hypergeometric 5 2 2 (by norm_num) (by norm_num)).toMeasure
    (upperTailPValue (hypergeometric 5 2 2 (by norm_num) (by norm_num)).toMeasure id) :=
  isValidPValue_upperTailPValue HasLaw.id

/-- Boundary: the upper tail at cutoff `0` is the total mass `1`. -/
example (ν : Measure ℕ) [IsProbabilityMeasure ν] : upperTail ν 0 = 1 := by
  simp [upperTail]

/-- Boundary: under a point mass at `3` the upper tail is `1` up to the atom and `0` above it,
so the p-value takes only the values `0` and `1`. -/
example : upperTail (Measure.dirac 3) 3 = 1 ∧ upperTail (Measure.dirac 3) 4 = 0 := by
  simp [upperTail, measureReal_def]

/-- The general theorem applies to any law on `ℕ`, e.g. a binomial count. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℕ} {n : ℕ}
    {p : unitInterval} (hX : HasLaw X Bin(n, p) μ) :
    IsValidPValue μ (upperTailPValue Bin(n, p) X) :=
  isValidPValue_upperTailPValue hX

end MathlibExtTest.Probability.Statistics.ExactTests.TailPValue
