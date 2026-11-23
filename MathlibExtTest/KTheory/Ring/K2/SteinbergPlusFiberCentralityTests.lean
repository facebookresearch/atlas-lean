/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.K2.SteinbergPlusFiberCentrality
import Batteries.Tactic.Lint

/-!
# Clients of original plus-fiber centrality

The original extension's left map and the canonical kernel dictionary both
give the same actual boundary classes. These clients recover their centrality
from the original projection kernel and its established central extension.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace MathlibExtTest.SteinbergPlusFiberCentrality

open AlgebraicKTheory.StableGL

#check @independentPlusFiberConnectingHom_range_le_center
#check @independentPlusFiberExtension_isCentral
#print axioms independentPlusFiberConnectingHom_range_le_center
#print axioms independentPlusFiberToStableE_ker_le_center
#print axioms independentPlusFiberExtension_isCentral

example (R : Type u) [Ring R]
    (a : HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    (independentPlusFiberKernelMulEquiv R a :
      FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R)) ∈
        Subgroup.center (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R)) :=
  independentPlusFiberToStableE_ker_le_center R (independentPlusFiberKernelMulEquiv R a).property

example (R : Type u) [Ring R]
    (a : HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R))
    (g : FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R)) :
    Commute g ((independentPlusFiberExtension R).inl a) := by
  have hker : (independentPlusFiberExtension R).inl a ∈
      (independentPlusFiberExtension R).rightHom.ker := by
    rw [← (independentPlusFiberExtension R).range_inl_eq_ker_rightHom]
    exact ⟨a, rfl⟩
  exact (Subgroup.mem_center_iff.mp (independentPlusFiberExtension_isCentral R hker)) g

#lint only unusedArguments in MathlibExt.KTheory.Ring.K2.SteinbergPlusFiberCentrality

end MathlibExtTest.SteinbergPlusFiberCentrality
