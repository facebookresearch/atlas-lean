/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.SteinbergPlusFiberExtension

/-! # Clients of the actual plus-fiber extension and kernel dictionary -/

noncomputable section

universe u

namespace AlgebraicKTheory.StableGL

/-- The inverse dictionary gives the actual boundary preimage of an original kernel element. -/
theorem independentPlusFiberKernel_inverse_test (R : Type u) [Ring R]
    (x : (independentPlusFiberToStableE R).ker) :
    independentPlusFiberConnectingHom R ((independentPlusFiberKernelMulEquiv R).symm x) =
      (x : FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R)) :=
  independentPlusFiberKernelMulEquiv_symm_coe R x

/-- Every original fiber loop killed in `StableE` has a unique actual cube-two preimage. -/
theorem independentPlusFiber_unique_boundary_preimage_test (R : Type u) [Ring R]
    (z : FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
    (hz : independentPlusFiberToStableE R z = 1) :
    ∃! a : HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R),
      independentPlusFiberConnectingHom R a = z := by
  let x : (independentPlusFiberToStableE R).ker := ⟨z, hz⟩
  have hx := independentPlusFiberKernelMulEquiv_symm_coe R x
  refine ⟨(independentPlusFiberKernelMulEquiv R).symm x, hx, ?_⟩
  intro a ha
  exact independentPlusFiberConnectingHom_injective R (ha.trans hx.symm)

end AlgebraicKTheory.StableGL

end
