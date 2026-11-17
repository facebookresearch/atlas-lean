/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil

@[expose] public section

open MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil

namespace MathlibExtTest.Analysis.Numerical.PeriodicLeapfrogStencil

/-- The nonconstant `N = 3` example has adjoint pairing `-5`, wrong-sign pairing `+5`. -/
example : weightedInner (1 / 2) (dPlus (1 / 2) ![1, 2, 4]) ![3, -1, 2] = -5 ∧
    weightedInner (1 / 2) ![1, 2, 4] (-dMinus (1 / 2) ![3, -1, 2]) = -5 ∧
    weightedInner (1 / 2) ![1, 2, 4] (dMinus (1 / 2) ![3, -1, 2]) = 5 :=
  example_adjoint_sign

/-- The no-wrap difference is not the weighted adjoint on the `N = 3` witness. -/
example : ¬ IsWeightedAdjoint (1 / 2) (dPlusNoWrap (N := 3) (1 / 2)) (-dMinus (1 / 2)) :=
  noWrap_not_weightedAdjoint

end MathlibExtTest.Analysis.Numerical.PeriodicLeapfrogStencil
