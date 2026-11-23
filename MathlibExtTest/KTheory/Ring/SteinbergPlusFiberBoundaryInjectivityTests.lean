/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.SteinbergPlusFiberBoundaryInjectivity

/-! # Clients of the original plus-fiber boundary injection -/

noncomputable section

universe u

namespace AlgebraicKTheory.StableGL

/-- Equality of original connecting images detects equality of the same cube-based classes. -/
theorem independentPlusFiberConnecting_eq_iff_test (R : Type u) [Ring R]
    (a b : HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    independentPlusFiberConnectingHom R a = independentPlusFiberConnectingHom R b ↔ a = b :=
  ⟨fun h => independentPlusFiberConnectingHom_injective R h,
    fun h => congrArg (independentPlusFiberConnectingHom R) h⟩

/-- Every original ordinary-BGL cube-two class is the unit at that actual point. -/
theorem ordinaryBGL_piTwo_unit_test (R : Type u) [Ring R]
    (x : ordinaryBGL R) (a : HomotopyGroup.Pi 2 (ordinaryBGL R) x) : a = 1 :=
  (ordinaryBGL_piTwo_subsingleton R x).elim a 1

end AlgebraicKTheory.StableGL

end
