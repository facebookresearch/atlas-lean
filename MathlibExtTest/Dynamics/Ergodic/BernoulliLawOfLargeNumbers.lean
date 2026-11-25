/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.BernoulliLawOfLargeNumbers
public import Mathlib.Probability.UniformOn

import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology
open MathlibExt.Dynamics.Ergodic.BernoulliLawOfLargeNumbers
open MathlibExt.Dynamics.Ergodic.BernoulliShift

namespace MathlibExtTest.Dynamics.Ergodic.BernoulliLawOfLargeNumbers

-- Birkhoff averages of the first coordinate are empirical means.
example (x : ℕ → ℕ) :
    birkhoffAverage ℝ shift (fun y : ℕ → ℕ => (y 0 : ℝ)) 2 x = (2 : ℝ)⁻¹ * (x 0 + x 1) := by
  rw [birkhoffAverage_shift_eval_zero]
  simp [Finset.sum_range_succ]

-- Strong law of large numbers for fair coin tosses: the frequency of heads converges a.s.
example :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => ProbabilityTheory.uniformOn (Set.univ : Set Bool)),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (if x k then (1 : ℝ) else 0))
        atTop (𝓝 (∫ b, (if b then (1 : ℝ) else 0)
          ∂ProbabilityTheory.uniformOn (Set.univ : Set Bool))) :=
  tendsto_average_coordinates_ae _ (Integrable.of_finite)

end MathlibExtTest.Dynamics.Ergodic.BernoulliLawOfLargeNumbers
