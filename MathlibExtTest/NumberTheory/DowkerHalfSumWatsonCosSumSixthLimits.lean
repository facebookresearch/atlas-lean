/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DowkerHalfSumWatsonCosSumSixthLimits

namespace MathlibExtTest.NumberTheory.DowkerHalfSumWatsonCosSumSixthLimits

open MetaMathlibExt Filter
open scoped Topology

-- The two vanishing sequences sum to a vanishing sequence.
example : Tendsto (fun m : ℕ => watsonCosSum (6 * m) m + watsonCosSum (6 * m) (5 * m))
    atTop (𝓝 0) := by
  simpa using watson_cos_sum_sixth_limits.1.add watson_cos_sum_sixth_limits.2

-- Concretely, the first sequence is eventually bounded by one in norm.
example : ∀ᶠ m : ℕ in atTop, ‖watsonCosSum (6 * m) m‖ < 1 := by
  have hn : Tendsto (fun m : ℕ => ‖watsonCosSum (6 * m) m‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp watson_cos_sum_sixth_limits.1
  exact hn.eventually (eventually_lt_nhds zero_lt_one)

end MathlibExtTest.NumberTheory.DowkerHalfSumWatsonCosSumSixthLimits
