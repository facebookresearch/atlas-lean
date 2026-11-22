/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.FiniteActivePopulation.Moment

/-! Tests: the closure counterexample values. -/

namespace MathlibExtTest.Biology.Dynamics.FiniteActivePopulation.Moment

open MathlibExt.Biology.Dynamics.FiniteActivePopulation.Moment

/-- Exact rate `0`, closure `1/4`, mean `1`. -/
example : (∑ i : Fin 3, momentWitness i * ((2 - (i : ℝ)) * ((i : ℝ) / 2) ^ 2)) = 0 ∧
    (2 - (1 : ℝ)) * ((1 : ℝ) / 2) ^ 2 = 1 / 4 :=
  ⟨moment_closure_counterexample.1, moment_closure_counterexample.2.1⟩

/-- The witness is a probability law: nonnegative with total mass one. -/
example : (∑ i : Fin 3, momentWitness i) = 1 ∧ ∀ i, 0 ≤ momentWitness i :=
  ⟨momentWitness_sum_one, momentWitness_nonneg⟩

end MathlibExtTest.Biology.Dynamics.FiniteActivePopulation.Moment
