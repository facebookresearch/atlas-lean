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

import MathlibExt.CategoryTheory.Equivalence.FunctorFamily
import Batteries.Tactic.Lint

set_option autoImplicit false
noncomputable section
universe uA vA uC vC uD vD

open CategoryTheory

variable {A : Type uA} [Category.{vA} A]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (E : C ≌ D) (P : A ⥤ C ⥤ C) (H : A ⥤ D ⥤ D)
  (e : ∀ (K : A) (Z : D), (P.obj K).obj (E.inverse.obj Z) ≅
    E.inverse.obj ((H.obj K).obj Z))
  (ht : ∀ (K : A) {Z Z' : D} (f : Z ⟶ Z'),
    (P.obj K).map (E.inverse.map f) ≫ (e K Z').hom =
      (e K Z).hom ≫ E.inverse.map ((H.obj K).map f))
  (hc : ∀ {K K' : A} (i : K ⟶ K') (Z : D),
    (P.map i).app (E.inverse.obj Z) ≫ (e K' Z).hom =
      (e K Z).hom ≫ E.inverse.map ((H.map i).app Z))

-- Both maps retain the original component comparison and the chosen counit.
example (K : A) (Z : D) :
    ((Equivalence.conjugateFamilyIso E P H e ht hc).hom.app K).app Z =
      E.functor.map (e K Z).hom ≫ E.counitIso.hom.app ((H.obj K).obj Z) :=
  Equivalence.conjugateFamilyIso_hom_app_app E P H e ht hc K Z

example (K : A) (Z : D) :
    ((Equivalence.conjugateFamilyIso E P H e ht hc).inv.app K).app Z =
      E.counitIso.inv.app ((H.obj K).obj Z) ≫ E.functor.map (e K Z).inv :=
  Equivalence.conjugateFamilyIso_inv_app_app E P H e ht hc K Z

example (K : A) (Z : D) :
    (Equivalence.conjugateObjIso E (P.obj K) (H.obj K) Z (e K Z)).hom =
      E.functor.map (e K Z).hom ≫ E.counitIso.hom.app ((H.obj K).obj Z) := by simp

example (K : A) (Z : D) :
    (Equivalence.conjugateObjIso E (P.obj K) (H.obj K) Z (e K Z)).inv =
      E.counitIso.inv.app ((H.obj K).obj Z) ≫ E.functor.map (e K Z).inv := by simp

example (K : A) (Z : D) :
    (Equivalence.conjugateNatIso E (P.obj K) (H.obj K) (e K) (ht K)).hom.app Z =
      E.functor.map (e K Z).hom ≫ E.counitIso.hom.app ((H.obj K).obj Z) := by simp

example (K : A) (Z : D) :
    (Equivalence.conjugateNatIso E (P.obj K) (H.obj K) (e K) (ht K)).inv.app Z =
      E.counitIso.inv.app ((H.obj K).obj Z) ≫ E.functor.map (e K Z).inv := by simp

-- The complete maps are natural in every target arrow and parameter arrow.
example (K : A) {Z Z' : D} (f : Z ⟶ Z') :
    E.functor.map ((P.obj K).map (E.inverse.map f)) ≫
        ((Equivalence.conjugateFamilyIso E P H e ht hc).hom.app K).app Z' =
      ((Equivalence.conjugateFamilyIso E P H e ht hc).hom.app K).app Z ≫
        (H.obj K).map f :=
  ((Equivalence.conjugateFamilyIso E P H e ht hc).hom.app K).naturality f

example {K K' : A} (i : K ⟶ K') (Z : D) :
    E.functor.map ((P.map i).app (E.inverse.obj Z)) ≫
        ((Equivalence.conjugateFamilyIso E P H e ht hc).hom.app K').app Z =
      ((Equivalence.conjugateFamilyIso E P H e ht hc).hom.app K).app Z ≫
        (H.map i).app Z :=
  congrArg (fun t => t.app Z) ((Equivalence.conjugateFamilyIso E P H e ht hc).hom.naturality i)

example (K : A) {Z Z' : D} (f : Z ⟶ Z') :
    (H.obj K).map f ≫ ((Equivalence.conjugateFamilyIso E P H e ht hc).inv.app K).app Z' =
      ((Equivalence.conjugateFamilyIso E P H e ht hc).inv.app K).app Z ≫
        E.functor.map ((P.obj K).map (E.inverse.map f)) :=
  ((Equivalence.conjugateFamilyIso E P H e ht hc).inv.app K).naturality f

example {K K' : A} (i : K ⟶ K') (Z : D) :
    (H.map i).app Z ≫ ((Equivalence.conjugateFamilyIso E P H e ht hc).inv.app K').app Z =
      ((Equivalence.conjugateFamilyIso E P H e ht hc).inv.app K).app Z ≫
        E.functor.map ((P.map i).app (E.inverse.obj Z)) :=
  congrArg (fun t => t.app Z) ((Equivalence.conjugateFamilyIso E P H e ht hc).inv.naturality i)

example (K : A) (Z : D) :
    ((Equivalence.conjugateFamilyIso E P H e ht hc).hom.app K).app Z ≫
        ((Equivalence.conjugateFamilyIso E P H e ht hc).inv.app K).app Z = 𝟙 _ :=
  (Equivalence.conjugateFamilyIso E P H e ht hc).app K |>.hom_inv_id_app Z

example (K : A) (Z : D) :
    ((Equivalence.conjugateFamilyIso E P H e ht hc).inv.app K).app Z ≫
        ((Equivalence.conjugateFamilyIso E P H e ht hc).hom.app K).app Z = 𝟙 _ :=
  (Equivalence.conjugateFamilyIso E P H e ht hc).app K |>.inv_hom_id_app Z

#print axioms CategoryTheory.Equivalence.conjugateObjIso
#print axioms CategoryTheory.Equivalence.conjugateNatIso
#print axioms CategoryTheory.Equivalence.conjugateFamilyIso
#print axioms CategoryTheory.Equivalence.conjugateObjIso_hom
#print axioms CategoryTheory.Equivalence.conjugateObjIso_inv
#print axioms CategoryTheory.Equivalence.conjugateNatIso_hom_app
#print axioms CategoryTheory.Equivalence.conjugateNatIso_inv_app
#print axioms CategoryTheory.Equivalence.conjugateFamilyIso_hom_app_app
#print axioms CategoryTheory.Equivalence.conjugateFamilyIso_inv_app_app
#lint only unusedArguments in MathlibExt.CategoryTheory.Equivalence.FunctorFamily
#lint in MathlibExt.CategoryTheory.Equivalence.FunctorFamily
