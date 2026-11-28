/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.LebesgueUniversalCoveringConstantPal1920HexagonUpperBoundHolds

/-! # Tests for Pál's hexagon bound on Lebesgue's universal covering constant -/

namespace MathlibExtTest.Geometry.LebesgueUniversalCoveringConstantPal1920HexagonUpperBoundHolds

open MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

example : lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal (Real.sqrt 3 / 2) :=
  pal1920HexagonUpperBound_holds

-- The upper bound rules out the infinite value of the infimum of an empty family.
example : lebesgueUniversalCoveringConstant < ⊤ :=
  pal1920HexagonUpperBound_holds.trans_lt ENNReal.ofReal_lt_top

end MathlibExtTest.Geometry.LebesgueUniversalCoveringConstantPal1920HexagonUpperBoundHolds
