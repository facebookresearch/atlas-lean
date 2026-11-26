/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonSum

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MathlibExtTest.Probability.Distributions.PoissonSum

/-- Non-vacuity: three independent Poisson variables with rates `1, 2, 3` sum to `Poisson(6)`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {K : Fin 3 → Ω → ℕ}
    (hind : iIndepFun K P) (hmeas : ∀ i, Measurable (K i))
    (hlaw : ∀ i, HasLaw (K i) Po((i : ℝ≥0) + 1) P) :
    HasLaw (∑ i, K i) Po(∑ i : Fin 3, ((i : ℝ≥0) + 1)) P :=
  hind.hasLaw_sum_poissonMeasure_of_nonempty hmeas (fun i _ => hlaw i) univ_nonempty

end MathlibExtTest.Probability.Distributions.PoissonSum
