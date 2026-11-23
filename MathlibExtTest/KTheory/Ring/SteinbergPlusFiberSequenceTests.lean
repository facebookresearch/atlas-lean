/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.SteinbergPlusFiberSequence

/-! # Clients of the original plus-fiber sequence -/

noncomputable section

universe u

namespace AlgebraicKTheory.StableGL

/-- The ordinary fiber projection kills the original cube-based connecting class. -/
theorem independentPlusFiberConnecting_projection_test (R : Type u) [Ring R]
    (a : HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    independentPlusFiberProjection R (independentPlusFiberConnectingHom R a) = 1 :=
  independentPlusFiberProjection_connecting R a

/-- Every elementary matrix with its original coefficient has an actual fiber-loop lift. -/
theorem independentPlusFiber_elementary_lift_test (R : Type u) [Ring R]
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : R) :
    ∃ g : FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R),
      independentPlusFiberToStableE R g = StableE.elementary n i j hij a :=
  independentPlusFiberToStableE_surjective R (StableE.elementary n i j hij a)

/-- The point keeps the complete literal constant path at the original plus point. -/
theorem independentPlusFiber_point_path_test (R : Type u) [Ring R] :
    TopCat.homotopyFiberPath (independentBGLCellInclusion R) (independentBGLCellPoint R)
      (independentPlusFiberPoint R) = ContinuousMap.const TopCat.I (independentBGLCellPoint R) :=
  independentPlusFiberPoint_path R

end AlgebraicKTheory.StableGL

end
