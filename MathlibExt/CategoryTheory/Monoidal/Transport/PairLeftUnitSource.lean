/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The original pair and left unit under monoidal transport

The complete original source maps, carrier unit and counit, and coefficient
arrows are retained throughout the displayed identities.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory MonoidalCategory

namespace CategoryTheory.Monoidal.TransportPairSource
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D]

private theorem tensor_leftUnit {F G T : C} (f : F ⟶ 𝟙_ C) (g : G ⟶ T) :
    (f ⊗ₘ g) ≫ (λ_ T).hom = (f ▷ G) ≫ (λ_ G).hom ≫ g := by
  rw [tensorHom_def, Category.assoc, leftUnitor_naturality]

/-- The actual transported left-unit pair retains the original carrier unit,
counit, both input maps, pair inverse and target unitor. -/
theorem pairInverse_leftUnit (E : C ≌ D) {F G H : C} {A B T : D}
    (eF : F ≅ E.inverse.obj A) (eG : G ≅ E.inverse.obj B)
    (o : E.functor.obj H ≅ T) (p : F ⊗ G ≅ H)
    (l : A ⟶ E.functor.obj (𝟙_ C)) :
    letI : MonoidalCategory D := Monoidal.transport E
    (o.inv ≫ E.functor.map p.inv ≫ E.functor.map (eF.hom ⊗ₘ eG.hom)) ≫
        (l ▷ B) ≫ (λ_ B).hom =
      o.inv ≫ E.functor.map
        (p.inv ≫ ((eF.hom ≫ E.inverse.map l ≫ (E.unitIso.app (𝟙_ C)).inv) ▷ G) ≫
          (λ_ G).hom) ≫ E.functor.map eG.hom ≫ E.counitIso.hom.app B := by
  let : MonoidalCategory D := Monoidal.transport E
  let j := (E.unitIso.app (𝟙_ C)).inv
  have h : (eF.hom ⊗ₘ eG.hom) ≫ (E.inverse.map l ▷ E.inverse.obj B) ≫
      (j ▷ E.inverse.obj B) ≫ (λ_ (E.inverse.obj B)).hom =
      ((eF.hom ≫ E.inverse.map l ≫ j) ▷ G) ≫ (λ_ G).hom ≫ eG.hom := by
    rw [← tensorHom_id, ← tensorHom_id,
      ← Category.assoc (eF.hom ⊗ₘ eG.hom) (E.inverse.map l ⊗ₘ 𝟙 _),
      tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
    rw [← Category.assoc ((eF.hom ≫ E.inverse.map l) ⊗ₘ eG.hom)
      (j ⊗ₘ 𝟙 _), tensorHom_comp_tensorHom, Category.comp_id]
    simpa only [Category.assoc] using tensor_leftUnit (eF.hom ≫ E.inverse.map l ≫ j) eG.hom
  change (o.inv ≫ E.functor.map p.inv ≫ E.functor.map (eF.hom ⊗ₘ eG.hom)) ≫
    E.functor.map (E.inverse.map l ▷ E.inverse.obj B) ≫
    (E.functor.map ((j ▷ E.inverse.obj B) ≫ (λ_ (E.inverse.obj B)).hom) ≫
      E.counitIso.hom.app B) = _
  simp only [Functor.map_comp, Category.assoc]
  have hh := congrArg (fun f => o.inv ≫ E.functor.map p.inv ≫
    E.functor.map f ≫ E.counitIso.hom.app B) h
  simpa only [Functor.map_comp, Category.assoc] using hh

end CategoryTheory.Monoidal.TransportPairSource
