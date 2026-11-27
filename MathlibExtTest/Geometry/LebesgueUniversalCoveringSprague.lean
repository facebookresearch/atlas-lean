/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.LebesgueUniversalCoveringSprague

/-! # Tests for Sprague's bound on Lebesgue's universal covering constant -/

open MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

example : lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.844137708436 :=
  sprague1936UpperBound_holds

-- The bound is finite in the extended nonnegative reals.
example : lebesgueUniversalCoveringConstant < ⊤ :=
  sprague1936UpperBound_holds.trans_lt ENNReal.ofReal_lt_top
