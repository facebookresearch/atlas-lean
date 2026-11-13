/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.PoissonLikelihood

/-!
# Tests for the log-likelihood of independent Poisson counts

The log-likelihood of a concrete count vector, the same value as a log-probability under the
joint law of independent Poisson counts, and the junk value at a zero mean.
-/

open MeasureTheory ProbabilityTheory Real

namespace MathlibExtTest.Probability.Statistics.PoissonLikelihood

open MathlibExt.Probability.Statistics.PoissonLikelihood

/-- The log-likelihood of counts `(2, 0)` at means `(1, 1)` is `-2 - log 2`. -/
example : poissonLogLik (fun _ : Fin 2 => (1 : ℝ)) ![2, 0] = -2 - log 2 := by
  simp [poissonLogLik, Fin.sum_univ_two]

/-- Two independent `Poisson(1)` counts give the count vector `(2, 0)` the log-probability
`-2 - log 2`. -/
example : log ((Measure.pi fun _ : Fin 2 => poissonMeasure 1).real {![2, 0]}) = -2 - log 2 := by
  rw [log_pi_poissonMeasure_real_singleton _ (fun _ => one_pos)]
  simp [poissonLogLik, Fin.sum_univ_two]

/-- The joint law of one Poisson count of mean `1` gives the count `0` the probability `e^{-1}`. -/
example : (Measure.pi fun _ : Unit => poissonMeasure 1).real {fun _ => 0} = exp (-1) := by
  rw [pi_poissonMeasure_real_singleton]
  simp

/-- Junk value outside the domain: at a zero mean, `log 0 = 0` makes a count of `1` cost
nothing, although its probability is `0`. -/
example : poissonLogLik (fun _ : Unit => (0 : ℝ)) (fun _ => 1) = 0 := by
  simp [poissonLogLik]

end MathlibExtTest.Probability.Statistics.PoissonLikelihood
