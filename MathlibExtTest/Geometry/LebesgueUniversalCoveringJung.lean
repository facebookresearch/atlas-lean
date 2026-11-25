/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.LebesgueUniversalCoveringJung

/-! # Tests for Jung's bound on Lebesgue's universal covering constant -/

open MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

example : lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal (Real.pi / 3) :=
  trivialJungElekes1994UpperBound_holds

-- The upper bound rules out the infinite value of the infimum of an empty family.
example : lebesgueUniversalCoveringConstant < ⊤ :=
  trivialJungElekes1994UpperBound_holds.trans_lt ENNReal.ofReal_lt_top
