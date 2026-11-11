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
public import MathlibExt.Probability.Distributions.Multinomial

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
so the p-value takes only the values `0` and `1`, for every count `X` and outcome `ω`. -/
example {Ω : Type*} (X : Ω → ℕ) (ω : Ω) :
    upperTailPValue (Measure.dirac 3) X ω = if X ω ≤ 3 then 1 else 0 := by
  simp only [upperTailPValue, upperTail, measureReal_def]
  split_ifs with h <;> simp [Set.indicator, h]

/-- The general theorem applies to any law on `ℕ`, e.g. a binomial count. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℕ} {n : ℕ}
    {p : unitInterval} (hX : HasLaw X Bin(n, p) μ) :
    IsValidPValue μ (upperTailPValue Bin(n, p) X) :=
  isValidPValue_upperTailPValue hX

/-- The conditional test for two Poisson rates: for independent `X ~ Po(a)`, `Y ~ Po(b)`, the
upper-tail p-value of `X` under `Bin(N, a / (a + b))` is valid given the total `X + Y = N`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℕ} {a b : NNReal}
    (hab : 0 < a + b) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : HasLaw X (poissonMeasure a) μ) (hY : HasLaw Y (poissonMeasure b) μ)
    (hXY : IndepFun X Y μ) (N : ℕ) :
    IsValidPValue (μ[|{ω | X ω + Y ω = N}])
      (upperTailPValue (binomial N ⟨(a : ℝ) / (a + b), by positivity,
        div_le_one_of_le₀ (le_add_of_nonneg_right b.2) (by positivity)⟩) X) :=
  isValidPValue_upperTailPValue (hasLaw_cond_binomial hab hXm hYm hX hY hXY N)

end MathlibExtTest.Probability.Statistics.ExactTests.TailPValue
