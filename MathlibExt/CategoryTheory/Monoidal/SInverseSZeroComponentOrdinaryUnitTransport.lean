/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentHSpace
public import MathlibExt.CategoryTheory.Monoidal.SInverseSComponentSpace
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso

/-!
# The original ordinary zero-unit fundamental group

The existing native weak-unit structure proves commutativity at its actual
zero object. The canonical underlying-Top realization Iso transports that
result to the literal ordinary zeroSpacePoint. All maps are the original
homeomorphism maps, and no target H-space or commutativity premise is input.

This is the point/fundamental-group transport. Constructing a raw-product
ordinary HSpace still requires the actual product comparison and both
point-relative unit families; it is not inferred from this theorem.
-/

noncomputable section

open CategoryTheory Limits ZeroObject

universe u v

public section

namespace CategoryTheory.SInverseS.ComponentTranslation

private theorem fundamentalGroup_mul_comm_of_homeomorph
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (y : Y) (hxy : e x = y)
    (hX : ∀ a b : FundamentalGroup X x, a * b = b * a)
    (p q : FundamentalGroup Y y) : p * q = q * p := by
  let E : FundamentalGroup X x ≃* FundamentalGroup Y y :=
    FundamentalGroup.mulEquivOfHomeomorphAt e x y hxy
  have h := congrArg (fun a : FundamentalGroup X x => E a)
    (hX (E.symm p) (E.symm q))
  simpa only [map_mul, E.apply_symm_apply] using h

/-- The fundamental group of the ORIGINAL ordinary zero component is
commutative at its literal realized zero-object point. This is derived from
the original native weak-unit data and canonical point-preserving Iso. -/
theorem zeroSpace_fundamentalGroup_mul_comm
    {C : Type u} [Category.{u} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (p q : FundamentalGroup (zeroSpace (C := C)) (zeroSpacePoint (C := C))) :
    p * q = q * p := by
  let X : CGWH.{u, u} := zeroComponentClassifyingSpace.{u} C
  let x : X := zeroComponentBasepoint.{u} C
  let d : CGWH.cgwhToTop.obj X ≅ zeroSpace (C := C) :=
    classifyingSpaceCGWHToTopIso.{u, u, u}.app (Cat.of (ZeroComponent (C := C)))
  let e : X ≃ₜ zeroSpace (C := C) := TopCat.homeoOfIso d
  have hPoint : e x = zeroSpacePoint (C := C) :=
    (classifyingSpaceCGWHPoint_toTop.{u, u, u}
      (zeroComponentBaseObject (C := C))).trans
        (zeroSpacePoint_eq_realizedVertex (C := C)).symm
  have hX : ∀ a b : FundamentalGroup X x, a * b = b * a :=
    zeroComponentClassifyingSpace_fundamentalGroup_mul_comm.{u} C
  exact fundamentalGroup_mul_comm_of_homeomorph e x
    (zeroSpacePoint (C := C)) hPoint hX p q

end CategoryTheory.SInverseS.ComponentTranslation

end
