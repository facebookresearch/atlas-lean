/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Softplus

/-!
# Tests for `Real.softplus`

The value at `0` is `log 2`, the slope at `0` is `1 / 2`, and convexity gives the midpoint
inequality.
-/

namespace MathlibExtTest.Softplus

example : Real.softplus 0 = Real.log 2 := by
  norm_num [Real.softplus]

example : HasDerivAt Real.softplus (1 / 2) 0 := by
  simpa using Real.hasDerivAt_softplus 0

example (a b : ℝ) :
    Real.softplus ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b)
      ≤ (1 / 2 : ℝ) • Real.softplus a + (1 / 2 : ℝ) • Real.softplus b :=
  Real.convexOn_softplus.2 (Set.mem_univ a) (Set.mem_univ b) (by norm_num) (by norm_num)
    (by norm_num)

end MathlibExtTest.Softplus
