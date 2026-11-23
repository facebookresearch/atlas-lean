/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.ClassifyingSpace.CGWHWeakHSpace
public import
  MathlibExt.CategoryTheory.Monoidal.GroupCompletionSpace
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentBiprod

/-!
# Native weak H-space on the additive S⁻¹S zero component

Coordinatewise biproduct and its categorical unitors specialize the generic
categorical classifying-space construction to the zero component of additive
`S⁻¹S`.  The root path runs forward from the realized `(0 ⊞ 0, 0 ⊞ 0)`
vertex to the selected `(0,0)` vertex; no strict object-level unit equality
is asserted.

The result is a named weak-H-space structure and an explicit commutativity
theorem for the fundamental group.  No raw-product H-space or global
`CommGroup` instance is installed, and no kernel, homology, plus-construction,
or `Q = +` statement is made.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits ZeroObject

universe w u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The selected point of the native zero-component classifying space. -/
noncomputable def zeroComponentBasepoint :
    zeroComponentClassifyingSpace.{w} C :=
  classifyingSpaceCGWHPoint.{w}
    (zeroComponentBaseObject (C := C))

/-- Coordinatewise biproduct multiplication on the native zero-component
classifying space. -/
noncomputable def zeroComponentClassifyingSpaceMul :
    zeroComponentClassifyingSpace.{w} C ⨯
        zeroComponentClassifyingSpace.{w} C ⟶
      zeroComponentClassifyingSpace.{w} C :=
  categoricalClassifyingSpaceMul.{w}
    (ZeroComponent (C := C))
    (zeroComponentBiprodFunctor (C := C))

/-- The chosen forward root path from the product of the two selected unit
points to the selected unit point. -/
noncomputable def zeroComponentClassifyingSpaceRootPath :
    Path
      (zeroComponentClassifyingSpaceMul.{w} C
        (CGWH.prodPoint _ _
          (zeroComponentBasepoint.{w} C)
          (zeroComponentBasepoint.{w} C)))
      (zeroComponentBasepoint.{w} C) :=
  categoricalClassifyingSpaceRootPath.{w}
    (ZeroComponent (C := C))
    (zeroComponentBiprodFunctor (C := C))
    (zeroComponentBaseObject (C := C))
    (by
      change zeroComponentBiprodLeftUnitFunctor (C := C) ≅
        𝟭 (ZeroComponent (C := C))
      exact zeroComponentBiprodLeftUnitIso (C := C))

/-- Multiplication on realized zero-component object vertices is induced by
coordinatewise biproduct in the category. -/
@[simp]
theorem zeroComponentClassifyingSpaceMul_prodPoint
    (X Y : ZeroComponent (C := C)) :
    zeroComponentClassifyingSpaceMul.{w} C
        (CGWH.prodPoint _ _
          (classifyingSpaceCGWHPoint.{w} X)
          (classifyingSpaceCGWHPoint.{w} Y)) =
      classifyingSpaceCGWHPoint.{w}
        ((zeroComponentBiprodFunctor (C := C)).obj (X, Y)) :=
  categoricalClassifyingSpaceMul_prodPoint.{w}
    (ZeroComponent (C := C))
    (zeroComponentBiprodFunctor (C := C)) X Y

/-- In particular, multiplication of the two selected points lands at the
realized `0 ⊞ 0` pair vertex, before the root path returns to `(0,0)`. -/
@[simp]
theorem zeroComponentClassifyingSpaceMul_basepoint :
    zeroComponentClassifyingSpaceMul.{w} C
        (CGWH.prodPoint _ _
          (zeroComponentBasepoint.{w} C)
          (zeroComponentBasepoint.{w} C)) =
      classifyingSpaceCGWHPoint.{w}
        ((zeroComponentBiprodFunctor (C := C)).obj
          (zeroComponentBaseObject (C := C),
            zeroComponentBaseObject (C := C))) :=
  zeroComponentClassifyingSpaceMul_prodPoint.{w} C _ _

/-- Named weak-unit native CGWH H-space data on the additive `S⁻¹S` zero
component. -/
noncomputable def zeroComponentClassifyingSpaceWeakHSpaceData :
    CGWH.WeakHSpaceData (zeroComponentClassifyingSpace.{w} C) :=
  categoricalClassifyingSpaceWeakHSpaceData.{w}
    (ZeroComponent (C := C))
    (zeroComponentBiprodFunctor (C := C))
    (zeroComponentBaseObject (C := C))
    (by
      change zeroComponentBiprodLeftUnitFunctor (C := C) ≅
        𝟭 (ZeroComponent (C := C))
      exact zeroComponentBiprodLeftUnitIso (C := C))
    (by
      change zeroComponentBiprodRightUnitFunctor (C := C) ≅
        𝟭 (ZeroComponent (C := C))
      exact zeroComponentBiprodRightUnitIso (C := C))
    (by
      change (zeroComponentBiprodLeftUnitIso (C := C)).hom.app
          (zeroComponentBaseObject (C := C)) =
        (zeroComponentBiprodRightUnitIso (C := C)).hom.app
          (zeroComponentBaseObject (C := C))
      exact
        zeroComponentBiprodLeftUnitIso_hom_app_base_eq_right (C := C))

@[simp]
theorem zeroComponentClassifyingSpaceWeakHSpaceData_mul :
    (zeroComponentClassifyingSpaceWeakHSpaceData.{w} C).mul =
      zeroComponentClassifyingSpaceMul.{w} C :=
  rfl

@[simp]
theorem zeroComponentClassifyingSpaceWeakHSpaceData_e :
    (zeroComponentClassifyingSpaceWeakHSpaceData.{w} C).e =
      zeroComponentBasepoint.{w} C :=
  rfl

@[simp]
theorem zeroComponentClassifyingSpaceWeakHSpaceData_rootPath :
    (zeroComponentClassifyingSpaceWeakHSpaceData.{w} C).rootPath =
      zeroComponentClassifyingSpaceRootPath.{w} C :=
  rfl

/-- The fundamental group of the zero-component classifying space at its
selected point is commutative. -/
theorem zeroComponentClassifyingSpace_fundamentalGroup_mul_comm
    (p q : FundamentalGroup
      (CGWH.cgwhToTop.obj (zeroComponentClassifyingSpace.{w} C))
      (zeroComponentBasepoint.{w} C)) :
    p * q = q * p :=
  CGWH.WeakHSpaceData.fundamentalGroup_mul_comm
    (zeroComponentClassifyingSpaceWeakHSpaceData.{w} C) p q

end SInverseS
end CategoryTheory

end
