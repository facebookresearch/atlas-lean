/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.ShetPosterior

/-!
# Tests for the posterior of the heterozygous selection coefficient

The balance mean at a concrete point, its antitonicity, the posterior monotonicity under a
two-point prior on `s_het ∈ {1/100, 1/10}` (non-vacuity: a probability prior on `(0, ∞)`), and
under a Dirac prior.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open MathlibExt.Biology.StatisticalGenetics.ShetPosterior

namespace MathlibExtTest.Biology.StatisticalGenetics.ShetPosterior

/-- `n = 10⁵` chromosomes, `U = 10⁻⁶`, `s_het = 1/10`: the expected PTV count is `1`. -/
example : balanceMean 100000 (1 / 1000000) (1 / 10) = 1 := by
  norm_num [balanceMean]

/-- Stronger selection lowers the expected count. -/
example :
    balanceMean 100000 (1 / 1000000) (1 / 10) ≤ balanceMean 100000 (1 / 1000000) (1 / 100) :=
  balanceMean_antitoneOn (by norm_num) (by norm_num : (1 / 100 : ℝ) ∈ Ioi 0)
    (by norm_num : (1 / 10 : ℝ) ∈ Ioi 0) (by norm_num)

/-- The two-point prior `½ δ_{1/100} + ½ δ_{1/10}` is a probability measure on `(0, ∞)`. -/
noncomputable def twoPointPrior : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac (1 / 100) + (1 / 2 : ENNReal) • Measure.dirac (1 / 10)

/-- The two-point prior has total mass one. -/
instance : IsProbabilityMeasure twoPointPrior := by
  constructor
  simp only [twoPointPrior, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  exact ENNReal.add_halves 1

/-- The two-point prior is concentrated on `(0, ∞)`. -/
theorem twoPointPrior_compl : twoPointPrior (Ioi 0)ᶜ = 0 := by
  simp only [twoPointPrior, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ measurableSet_Ioi.compl,
    Measure.dirac_apply' _ measurableSet_Ioi.compl]
  simp [Set.indicator]

/-- Under the two-point prior, observing `3` PTVs instead of `0` does not raise the posterior
probability that `s_het > 1/20`. -/
example :
    posteriorTail twoPointPrior (poissonLik (balanceMean 100000 (1 / 1000000))) 3 (1 / 20) ≤
    posteriorTail twoPointPrior (poissonLik (balanceMean 100000 (1 / 1000000))) 0 (1 / 20) :=
  posteriorTail_balance_antitone twoPointPrior_compl (by norm_num) (by norm_num) (by norm_num) _

end MathlibExtTest.Biology.StatisticalGenetics.ShetPosterior
