/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import Mathlib.CategoryTheory.Equivalence

/-!
# Comparing families of endofunctors through an equivalence

Component comparisons on the inverse image of an equivalence produce a natural
isomorphism of the transported family. The transport itself uses Mathlib's
`Equivalence.congrLeft` and `Equivalence.congrRight`.
-/

set_option autoImplicit false
noncomputable section
universe uA vA uC vC uD vD

namespace CategoryTheory.Equivalence

variable {A : Type uA} [Category.{vA} A]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Carry an inverse-image component comparison to the original target object. -/
def conjugateObjIso (E : C ≌ D) (R : C ⥤ C) (H : D ⥤ D) (Z : D)
    (e : R.obj (E.inverse.obj Z) ≅ E.inverse.obj (H.obj Z)) :
    (((E.congrLeft (E := C)).trans (E.congrRight (E := D))).functor.obj R).obj Z ≅
      H.obj Z :=
  E.functor.mapIso e ≪≫ E.counitIso.app (H.obj Z)

/-- The forward object comparison keeps the original component and counit. -/
@[simp]
theorem conjugateObjIso_hom (E : C ≌ D) (R : C ⥤ C) (H : D ⥤ D) (Z : D)
    (e : R.obj (E.inverse.obj Z) ≅ E.inverse.obj (H.obj Z)) :
    (conjugateObjIso E R H Z e).hom = E.functor.map e.hom ≫ E.counitIso.hom.app (H.obj Z) := rfl

/-- The inverse object comparison keeps the inverse counit and component. -/
@[simp]
theorem conjugateObjIso_inv (E : C ≌ D) (R : C ⥤ C) (H : D ⥤ D) (Z : D)
    (e : R.obj (E.inverse.obj Z) ≅ E.inverse.obj (H.obj Z)) :
    (conjugateObjIso E R H Z e).inv = E.counitIso.inv.app (H.obj Z) ≫ E.functor.map e.inv := rfl

private theorem conjugateObjIso_square (E : C ≌ D)
    {R R' : C ⥤ C} {H H' : D ⥤ D}
    (Z Z' : D) (p : R'.obj (E.inverse.obj Z) ⟶ R.obj (E.inverse.obj Z'))
    (t : H'.obj Z ⟶ H.obj Z')
    (e : R.obj (E.inverse.obj Z') ≅ E.inverse.obj (H.obj Z'))
    (e' : R'.obj (E.inverse.obj Z) ≅ E.inverse.obj (H'.obj Z))
    (hp : p ≫ e.hom = e'.hom ≫ E.inverse.map t) :
    E.functor.map p ≫ (conjugateObjIso E R H Z' e).hom =
      (conjugateObjIso E R' H' Z e').hom ≫ t := by
  change E.functor.map p ≫ (E.functor.map e.hom ≫ E.counitIso.hom.app _) =
    (E.functor.map e'.hom ≫ E.counitIso.hom.app _) ≫ t
  rw [← Category.assoc, ← E.functor.map_comp, hp, E.functor.map_comp,
    Category.assoc]
  exact (congrArg (fun q => E.functor.map e'.hom ≫ q)
    (E.counitIso.hom.naturality t)).trans (Category.assoc _ _ _).symm

/-- A comparison natural on the inverse image gives a comparison of endofunctors. -/
def conjugateNatIso (E : C ≌ D) (R : C ⥤ C) (H : D ⥤ D)
    (e : ∀ Z : D, R.obj (E.inverse.obj Z) ≅ E.inverse.obj (H.obj Z))
    (ht : ∀ {Z Z' : D} (f : Z ⟶ Z'), R.map (E.inverse.map f) ≫ (e Z').hom =
      (e Z).hom ≫ E.inverse.map (H.map f)) :
    ((E.congrLeft (E := C)).trans (E.congrRight (E := D))).functor.obj R ≅ H :=
  NatIso.ofComponents (fun Z => conjugateObjIso E R H Z (e Z)) (fun f =>
    conjugateObjIso_square E _ _ _ _ _ _ (ht f))

/-- The forward natural comparison has the original component formula. -/
@[simp]
theorem conjugateNatIso_hom_app (E : C ≌ D) (R : C ⥤ C) (H : D ⥤ D)
    (e : ∀ Z : D, R.obj (E.inverse.obj Z) ≅ E.inverse.obj (H.obj Z))
    (ht : ∀ {Z Z' : D} (f : Z ⟶ Z'), R.map (E.inverse.map f) ≫ (e Z').hom =
      (e Z).hom ≫ E.inverse.map (H.map f)) (Z : D) :
    (conjugateNatIso E R H e ht).hom.app Z =
      E.functor.map (e Z).hom ≫ E.counitIso.hom.app (H.obj Z) := rfl

/-- The inverse natural comparison has the original inverse component formula. -/
@[simp]
theorem conjugateNatIso_inv_app (E : C ≌ D) (R : C ⥤ C) (H : D ⥤ D)
    (e : ∀ Z : D, R.obj (E.inverse.obj Z) ≅ E.inverse.obj (H.obj Z))
    (ht : ∀ {Z Z' : D} (f : Z ⟶ Z'), R.map (E.inverse.map f) ≫ (e Z').hom =
      (e Z).hom ≫ E.inverse.map (H.map f)) (Z : D) :
    (conjugateNatIso E R H e ht).inv.app Z =
      E.counitIso.inv.app (H.obj Z) ≫ E.functor.map (e Z).inv := rfl

/-- Comparisons natural in both the target and the parameter give an isomorphism
of the whole endofunctor family. -/
def conjugateFamilyIso (E : C ≌ D) (P : A ⥤ C ⥤ C) (H : A ⥤ D ⥤ D)
    (e : ∀ (K : A) (Z : D), (P.obj K).obj (E.inverse.obj Z) ≅
      E.inverse.obj ((H.obj K).obj Z))
    (ht : ∀ (K : A) {Z Z' : D} (f : Z ⟶ Z'),
      (P.obj K).map (E.inverse.map f) ≫ (e K Z').hom =
        (e K Z).hom ≫ E.inverse.map ((H.obj K).map f))
    (hc : ∀ {K K' : A} (i : K ⟶ K') (Z : D),
      (P.map i).app (E.inverse.obj Z) ≫ (e K' Z).hom =
        (e K Z).hom ≫ E.inverse.map ((H.map i).app Z)) :
    P ⋙ ((E.congrLeft (E := C)).trans (E.congrRight (E := D))).functor ≅ H :=
  NatIso.ofComponents (fun K => conjugateNatIso E (P.obj K) (H.obj K) (e K)
    (ht K)) (by
    intro K K' i
    apply NatTrans.ext
    funext Z
    exact conjugateObjIso_square E Z Z ((P.map i).app (E.inverse.obj Z))
      ((H.map i).app Z) (e K' Z) (e K Z) (hc i Z))

/-- The forward family comparison retains each original parameter and target component. -/
@[simp]
theorem conjugateFamilyIso_hom_app_app (E : C ≌ D) (P : A ⥤ C ⥤ C) (H : A ⥤ D ⥤ D)
    (e : ∀ (K : A) (Z : D), (P.obj K).obj (E.inverse.obj Z) ≅
      E.inverse.obj ((H.obj K).obj Z))
    (ht : ∀ (K : A) {Z Z' : D} (f : Z ⟶ Z'),
      (P.obj K).map (E.inverse.map f) ≫ (e K Z').hom =
        (e K Z).hom ≫ E.inverse.map ((H.obj K).map f))
    (hc : ∀ {K K' : A} (i : K ⟶ K') (Z : D),
      (P.map i).app (E.inverse.obj Z) ≫ (e K' Z).hom =
        (e K Z).hom ≫ E.inverse.map ((H.map i).app Z)) (K : A) (Z : D) :
    ((conjugateFamilyIso E P H e ht hc).hom.app K).app Z =
      E.functor.map (e K Z).hom ≫ E.counitIso.hom.app ((H.obj K).obj Z) := rfl

/-- The inverse family comparison retains each inverse counit and component. -/
@[simp]
theorem conjugateFamilyIso_inv_app_app (E : C ≌ D) (P : A ⥤ C ⥤ C) (H : A ⥤ D ⥤ D)
    (e : ∀ (K : A) (Z : D), (P.obj K).obj (E.inverse.obj Z) ≅
      E.inverse.obj ((H.obj K).obj Z))
    (ht : ∀ (K : A) {Z Z' : D} (f : Z ⟶ Z'),
      (P.obj K).map (E.inverse.map f) ≫ (e K Z').hom =
        (e K Z).hom ≫ E.inverse.map ((H.obj K).map f))
    (hc : ∀ {K K' : A} (i : K ⟶ K') (Z : D),
      (P.map i).app (E.inverse.obj Z) ≫ (e K' Z).hom =
        (e K Z).hom ≫ E.inverse.map ((H.map i).app Z)) (K : A) (Z : D) :
    ((conjugateFamilyIso E P H e ht hc).inv.app K).app Z =
      E.counitIso.inv.app ((H.obj K).obj Z) ≫ E.functor.map (e K Z).inv := rfl

end CategoryTheory.Equivalence
