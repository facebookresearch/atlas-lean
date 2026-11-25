/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.LebesgueUniversalCoveringHansen

/-! # Tests for Hansen's corrected upper bound -/

open MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

example :
    lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.844137708398 :=
  hansen1992CorrectedBBG2015UpperBound_holds

-- The exact decimal bound implies a strict bound at the next larger decimal.
example :
    lebesgueUniversalCoveringConstant < ENNReal.ofReal 0.844137708399 := by
  apply hansen1992CorrectedBBG2015UpperBound_holds.trans_lt
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
