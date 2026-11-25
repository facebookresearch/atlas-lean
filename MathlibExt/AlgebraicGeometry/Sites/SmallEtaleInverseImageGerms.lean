/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Sites.Point.SkyscraperGerms
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImageStalks

/-!
# Original germ coordinates of the constructed small étale inverse image
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w vC uC uA vA p
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- V1 rewrite checking required the actual skyscraper and product aliases.
/-- The inverse right mate has the inverse of the original base-change coordinate map. -/
theorem smallEtaleInverseImageCommonGeometricStalkRightIso_inv_app_π
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X)
    (M : AddCommGrpCat.{max u w}) (U : Y.Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).fiber.obj U) :
    ((smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} f x).inv.app M).hom.app
          (op U) ≫
        Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).fiber.obj U) => M) z =
      Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
          ((smallEtaleBaseChange f).obj U)) => M)
        ((smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).inv.app U z) := by
  let β := smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x
  let ρ := smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} f x
  have hz : β.hom.app U (β.inv.app U z) = z := by
    simpa only [types_comp_apply, types_id_apply] using
      types_congr_hom (β.inv_hom_id_app U) z
  have h := smallEtaleInverseImageCommonGeometricStalkRightIso_hom_app_π.{u, w}
    f x M U (β.inv.app U z)
  change (ρ.hom.app M).hom.app (op U) ≫
      Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
        ((smallEtaleBaseChange f).obj U)) => M) (β.inv.app U z) =
      Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).fiber.obj U) => M)
        (β.hom.app U (β.inv.app U z)) at h
  rw [hz] at h
  have hi : (ρ.inv.app M).hom.app (op U) ≫ (ρ.hom.app M).hom.app (op U) = 𝟙 _ := by
    exact congrArg (fun t => t.hom.app (op U)) (ρ.inv_hom_id_app M)
  change (ρ.inv.app M).hom.app (op U) ≫ _ = _
  erw [← h, ← Category.assoc, hi, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- V1 implicit rewriting could not see the same direct-image object aliases.
/-- The inverse of the same stalk comparison sends a germ through the actual
inverse-image adjunction unit and the actual base-change point. -/
theorem smallEtaleInverseImageCommonGeometricStalkIso_inv_original_germ
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}) (U : Y.Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).fiber.obj U) :
    (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).toPresheafFiber U z Q.obj ≫
        (smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x).inv.app Q =
      ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app (op U) ≫
        (smallEtaleGeometricPointCommon.{u, w} x).toPresheafFiber
          ((smallEtaleBaseChange f).obj U)
          ((smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).inv.app U z)
          ((smallEtaleInverseImage.{u, w} f).obj Q).obj := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} x
  let I := smallEtaleGeometricPointCommon.{u, w} (x ≫ f)
  let L := smallEtaleInverseImage.{u, w} f
  let D := smallEtaleDirectImage.{u, max u w} f
  let a := I.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let b := (smallEtaleInverseImageAdjunction.{u, w} f).comp
    Φ.skyscraperSheafAdjunction
  let κ := smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x
  let ρ := smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} f x
  let M := Φ.sheafFiber.obj (L.obj Q)
  let zT := (smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).inv.app U z
  have hk : (conjugateEquiv b a).symm ρ.inv = κ.inv := by
    change (conjugateEquiv b a).symm (conjugateEquiv b a κ.inv) = κ.inv
    exact (conjugateEquiv b a).symm_apply_apply κ.inv
  have hu := unit_conjugateEquiv_symm b a ρ.inv Q
  rw [hk] at hu
  have hL : ((b.unit.app Q) ≫ ρ.inv.app M).hom.app (op U) ≫
      Pi.π (fun (_ : I.fiber.obj U) => M) z =
      ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app (op U) ≫
        Φ.toPresheafFiber ((smallEtaleBaseChange f).obj U) zT (L.obj Q).obj := by
    change (b.unit.app Q).hom.app (op U) ≫
        ((ρ.inv.app M).hom.app (op U) ≫ Pi.π (fun (_ : I.fiber.obj U) => M) z) = _
    rw [smallEtaleInverseImageCommonGeometricStalkRightIso_inv_app_π]
    rw [Adjunction.comp_unit_app]
    change ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app (op U) ≫
        ((Φ.skyscraperSheafAdjunction.unit.app (L.obj Q)).hom.app
          (op ((smallEtaleBaseChange f).obj U)) ≫ Pi.π _ zT) = _
    exact congrArg (fun t =>
      ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app (op U) ≫ t)
      (Φ.skyscraperSheafAdjunction_unit_app_π (L.obj Q)
        ((smallEtaleBaseChange f).obj U) zT)
  have hR : ((a.unit.app Q) ≫ I.skyscraperSheafFunctor.map (κ.inv.app Q)).hom.app
      (op U) ≫ Pi.π (fun (_ : I.fiber.obj U) => M) z =
      I.toPresheafFiber U z Q.obj ≫ κ.inv.app Q := by
    change (a.unit.app Q).hom.app (op U) ≫
        (CategoryTheory.Limits.Pi.map (fun (_ : I.fiber.obj U) => κ.inv.app Q) ≫ Pi.π _ z) = _
    erw [CategoryTheory.Limits.Pi.map_π, ← Category.assoc]
    exact congrArg (fun t => t ≫ κ.inv.app Q)
      (I.skyscraperSheafAdjunction_unit_app_π Q U z)
  have hv := congrArg (fun t => t.hom.app (op U) ≫
    Pi.π (fun (_ : I.fiber.obj U) => M) z) hu
  exact hR.symm.trans (hv.symm.trans hL)

end AlgebraicGeometry.Scheme.DerivedSections

end
