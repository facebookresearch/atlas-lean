/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SphereHom

/-!
# Actual scalar-suspended sphere representatives

The original scalar suspension-loop adjunction and native all-degree
loop shift identify maps from the scalar suspension of the same sphere
with the next homotopy degree. Both functions retain the actual source
coefficient and every original pointed target map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SphereHom

attribute [local instance] PointedCGWH.modelCategory.allObjectsFibrant

private theorem originalSphere_isCofibrant (n : ℕ) : IsCofibrant (sphere.{u, v} n) := by
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  let _ : IsCofibrant freePoint.{u, v} :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := powerAdjunction n) inferInstance

local instance originalSphereCofibrant (n : ℕ) : IsCofibrant (sphere.{u, v} n) :=
  originalSphere_isCofibrant n

/-- The actual scalar suspension of the original sphere has the next-degree Hom
correspondence, via its unchanged adjunction and the original native loop shift. -/
def suspendedSpherePiHomEquiv (n : ℕ) (X : PointedCGWH.{u, v}) :
    PointedCGWH.piN (n + 1) X ≃
      ((toHomotopyCategory PointedCGWH).obj (PointedCGWH.suspension.obj (sphere n)) ⟶
        (toHomotopyCategory PointedCGWH).obj X) := by
  let _ : IsCofibrant (sphere.{u, v} n) := originalSphere_isCofibrant n
  exact ((NativeLoopShiftGeometry.nativeLoopPiShiftNatIso n).app X).toEquiv.symm.trans
    ((spherePiHomEquiv n (PointedCGWH.loop.obj X)).trans
      (QuillenOrdinaryHoHom.homEquiv PointedCGWH.suspensionLoopAdjunction (sphere n) X).symm)

/-- Every original target map commutes with the complete scalar-suspended correspondence. -/
theorem suspendedSpherePiHomEquiv_naturality (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) (x : PointedCGWH.piN (n + 1) X) :
    suspendedSpherePiHomEquiv n Y (PointedCGWH.piNMap (n + 1) f x) =
      suspendedSpherePiHomEquiv n X x ≫ (toHomotopyCategory PointedCGWH).map f := by
  let _ : IsCofibrant (sphere.{u, v} n) := originalSphere_isCofibrant n
  have hs := ConcreteCategory.congr_hom
    (NativeLoopShiftGeometry.nativeLoopPiShiftNatIso_inv_naturality n f) x
  change (QuillenOrdinaryHoHom.homEquiv PointedCGWH.suspensionLoopAdjunction (sphere n) Y).symm
      (spherePiHomEquiv n (PointedCGWH.loop.obj Y)
        ((NativeLoopShiftGeometry.nativeLoopPiShiftNatIso n).inv.app Y
          (PointedCGWH.piNMap (n + 1) f x))) =
    (QuillenOrdinaryHoHom.homEquiv PointedCGWH.suspensionLoopAdjunction (sphere n) X).symm
      (spherePiHomEquiv n (PointedCGWH.loop.obj X)
        ((NativeLoopShiftGeometry.nativeLoopPiShiftNatIso n).inv.app X x)) ≫
      (toHomotopyCategory PointedCGWH).map f
  change (NativeLoopShiftGeometry.nativeLoopPiShiftNatIso n).inv.app Y
      (PointedCGWH.piNMap (n + 1) f x) =
    PointedCGWH.piNMap n (PointedCGWH.loop.map f)
      ((NativeLoopShiftGeometry.nativeLoopPiShiftNatIso n).inv.app X x) at hs
  rw [hs, spherePiHomEquiv_naturality,
    QuillenOrdinaryHoHom.homEquiv_symm_naturality_right]

/-- Its inverse retains the same entire original target map. -/
theorem suspendedSpherePiHomEquiv_inverse_naturality (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (g : (toHomotopyCategory PointedCGWH).obj
      (PointedCGWH.suspension.obj (sphere n)) ⟶ (toHomotopyCategory PointedCGWH).obj X) :
    (suspendedSpherePiHomEquiv n Y).symm (g ≫ (toHomotopyCategory PointedCGWH).map f) =
      PointedCGWH.piNMap (n + 1) f ((suspendedSpherePiHomEquiv n X).symm g) := by
  apply (suspendedSpherePiHomEquiv n Y).injective
  rw [Equiv.apply_symm_apply, suspendedSpherePiHomEquiv_naturality, Equiv.apply_symm_apply]

/-- The next-degree scalar class is induced by the actual original suspension unit. -/
def sphereSuspensionClass (n : ℕ) (X : PointedCGWH.{u, v})
    (x : PointedCGWH.piN n X) : PointedCGWH.piN (n + 1) (PointedCGWH.suspension.obj X) :=
  (NativeLoopShiftGeometry.nativeLoopPiShiftNatIso n).hom.app
    (PointedCGWH.suspension.obj X)
    (PointedCGWH.piNMap n (PointedCGWH.suspensionLoopAdjunction.unit.app X) x)

/-- The original unit and inverse adjunct retain the complete scalar sphere representative. -/
theorem suspendedSpherePiHomEquiv_unit (n : ℕ) (X : PointedCGWH.{u, v})
    (x : PointedCGWH.piN n X) :
    suspendedSpherePiHomEquiv n (PointedCGWH.suspension.obj X)
        (sphereSuspensionClass n X x) =
      (QuillenOrdinaryHoHom.homEquiv PointedCGWH.suspensionLoopAdjunction (sphere n)
        (PointedCGWH.suspension.obj X)).symm
        (spherePiHomEquiv n X x ≫
          (toHomotopyCategory PointedCGWH).map
            (PointedCGWH.suspensionLoopAdjunction.unit.app X)) := by
  let _ : IsCofibrant (sphere.{u, v} n) := originalSphere_isCofibrant n
  change (QuillenOrdinaryHoHom.homEquiv PointedCGWH.suspensionLoopAdjunction (sphere n)
      (PointedCGWH.suspension.obj X)).symm
      (spherePiHomEquiv n (PointedCGWH.loop.obj (PointedCGWH.suspension.obj X))
        (((NativeLoopShiftGeometry.nativeLoopPiShiftNatIso n).app
            (PointedCGWH.suspension.obj X)).toEquiv.symm
          (((NativeLoopShiftGeometry.nativeLoopPiShiftNatIso n).app
              (PointedCGWH.suspension.obj X)).toEquiv
            (PointedCGWH.piNMap n (PointedCGWH.suspensionLoopAdjunction.unit.app X) x)))) = _
  rw [Equiv.symm_apply_apply, spherePiHomEquiv_naturality]
  rfl

end PointedCGWH.SphereHom
