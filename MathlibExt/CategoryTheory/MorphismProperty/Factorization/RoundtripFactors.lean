/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.Factorization.EquivalenceRoundtrip

/-!
# Original factor Arrows through the actual roundtrip

The full intermediate comparison recovers the original natural i and p maps
and their original caller factorization. Both factor Arrows retain the given
unit components and the original complete Arrow maps.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe uC vC uD vD
open CategoryTheory Functor

namespace CategoryTheory

/-- The actual inverse unit on the complete original Arrow. -/
def originalArrowUnitInv {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (e : C ≌ D) (a : Arrow C) :
    e.inverse.mapArrow.obj (e.functor.mapArrow.obj a) ⟶ a :=
  Arrow.homMk (e.unitIso.inv.app a.left) (e.unitIso.inv.app a.right)
    (by
      change e.unitIso.inv.app a.left ≫ a.hom =
        e.inverse.map (e.functor.map a.hom) ≫ e.unitIso.inv.app a.right
      simpa only [Functor.comp_map, Functor.id_map] using
        (e.unitIso.inv.naturality a.hom).symm)

/-- The supplied units and original first natural map recover the same original first map. -/
theorem originalMiddleRoundtrip_i {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (Z : Arrow C ⥤ C) (i : Arrow.leftFunc ⟶ Z)
    (e : C ≌ D) (a : Arrow C) :
    (e.unitIso.hom.app a.left ≫ e.inverse.map
      (e.counitIso.inv.app (e.functor.obj a.left) ≫
        e.functor.map (i.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))))) ≫
      (originalMiddleRoundtripIso Z e).hom.app a = i.app a := by
  rw [originalMiddleRoundtripIso_hom_app]
  change (e.unitIso.hom.app a.left ≫ e.inverse.map
    (e.counitIso.inv.app (e.functor.obj a.left) ≫
      e.functor.map (i.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))))) ≫
      e.unitIso.inv.app (Z.obj (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))) ≫
        Z.map (originalArrowUnitInv e a) = i.app a
  rw [e.inverse.map_comp]
  have hu : e.inverse.map (e.functor.map
      (i.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a)))) ≫
      e.unitIso.inv.app (Z.obj (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))) =
        e.unitIso.inv.app (e.inverse.obj (e.functor.obj a.left)) ≫
          i.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a)) :=
    e.unitIso.inv.naturality (i.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a)))
  have hi := i.naturality (originalArrowUnitInv e a)
  simp only [Category.assoc] at hi ⊢
  rw [← Category.assoc (e.inverse.map (e.functor.map _)) (e.unitIso.inv.app _) _, hu]
  simp only [Category.assoc]
  rw [← Category.assoc (e.inverse.map (e.counitIso.inv.app _)) (e.unitIso.inv.app _) _]
  change e.unitIso.hom.app a.left ≫
    (e.inverse.map (e.counitIso.inv.app (e.functor.obj a.left)) ≫
      e.unitIso.inv.app (e.inverse.obj (e.functor.obj a.left))) ≫
        (i.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a)) ≫
          Z.map (originalArrowUnitInv e a)) = i.app a
  have hUnit : e.inverse.map (e.counitIso.inv.app (e.functor.obj a.left)) ≫
      e.unitIso.inv.app (e.inverse.obj (e.functor.obj a.left)) = 𝟙 _ := by
    rw [← e.unit_app_inverse]
    exact e.unitIso.hom_inv_id_app _
  rw [hUnit]
  have hid := Category.id_comp
    (i.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a)) ≫
      Z.map (originalArrowUnitInv e a))
  have hc := congrArg (fun t => e.unitIso.hom.app a.left ≫ t) hid
  apply hc.trans
  rw [← hi]
  change e.unitIso.hom.app a.left ≫ e.unitIso.inv.app a.left ≫ i.app a = i.app a
  rw [← Category.assoc, e.unitIso.hom_inv_id_app, Category.id_comp]

/-- The supplied units and original second natural map recover the same original second map. -/
theorem originalMiddleRoundtrip_p {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (Z : Arrow C ⥤ C) (p : Z ⟶ Arrow.rightFunc)
    (e : C ≌ D) (a : Arrow C) :
    (originalMiddleRoundtripIso Z e).hom.app a ≫ p.app a =
      e.inverse.map
        (e.functor.map (p.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))) ≫
          e.counitIso.hom.app (e.functor.obj a.right)) ≫ e.unitIso.inv.app a.right := by
  rw [originalMiddleRoundtripIso_hom_app]
  change (e.unitIso.inv.app (Z.obj (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))) ≫
    Z.map (originalArrowUnitInv e a)) ≫ p.app a = _
  have hp : Z.map (originalArrowUnitInv e a) ≫ p.app a =
      p.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a)) ≫
        e.unitIso.inv.app a.right := p.naturality (originalArrowUnitInv e a)
  have hu : e.inverse.map (e.functor.map
      (p.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a)))) ≫
      e.unitIso.inv.app (e.inverse.obj (e.functor.obj a.right)) =
        e.unitIso.inv.app (Z.obj (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))) ≫
          p.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a)) :=
    e.unitIso.inv.naturality (p.app (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a)))
  have hUnit : e.inverse.map (e.counitIso.hom.app (e.functor.obj a.right)) =
      e.unitIso.inv.app (e.inverse.obj (e.functor.obj a.right)) :=
    (e.unitInv_app_inverse _).symm
  rw [Category.assoc, hp]
  rw [e.inverse.map_comp, hUnit]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ e.unitIso.inv.app a.right) hu.symm)

end CategoryTheory
