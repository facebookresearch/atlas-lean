/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.WaterFillingCertificate

@[expose] public section

open MathlibExt.Analysis.Convex.WaterFillingCertificate Finset

namespace MathlibExtTest.Analysis.Convex.WaterFillingCertificate

/-- Two active modes and one inactive mode attain the water-filling maximum. -/
example : IsMaxOn (sumRateBits ![(2 : ℝ), 1, 1 / 4]) (powerFeasible (3 / 2)) ![1, 1 / 2, 0] :=
  isMaxOn_twoActive_oneInactive

/-- Zero budget forces the zero allocation, which is optimal. -/
example : IsMaxOn (sumRateBits ![(2 : ℝ), 1]) (powerFeasible 0) 0 :=
  isMaxOn_zeroPower_example

end MathlibExtTest.Analysis.Convex.WaterFillingCertificate
