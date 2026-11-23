/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.SteinbergPlusFiberBoundaryInjectivity
import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# The actual plus-fiber extension of the stable elementary group

The left map is the original connecting homomorphism from the actual
cube-based second homotopy group of BGL plus. The total group is the
ordinary fundamental group of the same complete ending-path fiber, and
the right map is its original projection to `StableE R`.

The already proved injection, projection surjection, and exactness give
this group extension. A canonical multiplicative equivalence identifies
its kernel with that same second homotopy group, and its inclusion is
exactly the original connecting map.

These are the maps in Weibel, *The K-book*, IV.1.7, printed pages 264–265
(official PDF pages 272–273). Centrality and universality require subsequent
theorems.
-/

noncomputable section

universe u

namespace AlgebraicKTheory.StableGL

/-- Restricting the original fiber projection to `StableE` retains the exact boundary image. -/
theorem independentPlusFiberToStableE_ker (R : Type u) [Ring R] :
    (independentPlusFiberToStableE R).ker = (independentPlusFiberConnectingHom R).range := by
  unfold independentPlusFiberToStableE
  rw [MonoidHom.ker_comp_of_injective _ _ (BGLPlusSubgroup.mulEquivStableE R).injective,
    MonoidHom.ker_codRestrict]
  exact independentPlusFiberProjection_ker R

/-- The original group extension `1 → π₂(BGL⁺) → π₁(F) → E∞ → 1`, with its actual maps. -/
def independentPlusFiberExtension (R : Type u) [Ring R] :
    GroupExtension
      (HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R))
      (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
      (StableE R) where
  inl := independentPlusFiberConnectingHom R
  rightHom := independentPlusFiberToStableE R
  inl_injective := independentPlusFiberConnectingHom_injective R
  range_inl_eq_ker_rightHom := (independentPlusFiberToStableE_ker R).symm
  rightHom_surjective := independentPlusFiberToStableE_surjective R

/-- The actual second plus group is canonically the kernel of the actual fiber projection. -/
def independentPlusFiberKernelMulEquiv (R : Type u) [Ring R] :
    HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R) ≃*
      (independentPlusFiberToStableE R).ker :=
  MulEquiv.ofBijective
    ((independentPlusFiberConnectingHom R).codRestrict
      (independentPlusFiberToStableE R).ker (fun a => by
        rw [independentPlusFiberToStableE_ker R]
        exact ⟨a, rfl⟩))
    (by
      constructor
      · intro a b hab
        exact independentPlusFiberConnectingHom_injective R (congrArg Subtype.val hab)
      · intro x
        have hx : (x : FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R)) ∈
            (independentPlusFiberConnectingHom R).range := by
          rw [← independentPlusFiberToStableE_ker R]
          exact x.property
        obtain ⟨a, ha⟩ := hx
        exact ⟨a, Subtype.ext ha⟩)

/-- Kernel inclusion after the canonical equivalence is the unchanged original boundary. -/
@[simp]
theorem independentPlusFiberKernelMulEquiv_coe (R : Type u) [Ring R]
    (a : HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    (independentPlusFiberKernelMulEquiv R a :
      FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R)) =
        independentPlusFiberConnectingHom R a := rfl

/-- The inverse kernel dictionary returns the original connecting preimage. -/
@[simp]
theorem independentPlusFiberKernelMulEquiv_symm_coe (R : Type u) [Ring R]
    (x : (independentPlusFiberToStableE R).ker) :
    independentPlusFiberConnectingHom R ((independentPlusFiberKernelMulEquiv R).symm x) =
      (x : FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R)) :=
  (independentPlusFiberKernelMulEquiv_coe R
    ((independentPlusFiberKernelMulEquiv R).symm x)).symm.trans
    (congrArg Subtype.val ((independentPlusFiberKernelMulEquiv R).apply_symm_apply x))

end AlgebraicKTheory.StableGL

end
