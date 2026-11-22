/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.CommSq

/-!
# Interchange for a functor represented by left tensor

If an endofunctor is isomorphic to tensoring on the left by an object, the
monoidal associator compares its value on a tensor product with the tensor
product of its value on the first factor and the unchanged second factor.
The comparison retains both input maps and the complete given representation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.TensorRepresentedInterchange

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The associator moves a functor represented by left tensor through an arbitrary right tensor. -/
def interchange (A : C) (S : C ⥤ C) (e : MonoidalCategory.tensorLeft A ≅ S) (X Y : C) :
    S.obj (X ⊗ Y) ≅ S.obj X ⊗ Y :=
  (e.app (X ⊗ Y)).symm ≪≫ (α_ A X Y).symm ≪≫ whiskerRightIso (e.app X) Y

/-- The forward map retains the representation inverse, associator inverse and representation map. -/
theorem interchange_hom (A : C) (S : C ⥤ C) (e : MonoidalCategory.tensorLeft A ≅ S) (X Y : C) :
    (interchange A S e X Y).hom =
      e.inv.app (X ⊗ Y) ≫ (α_ A X Y).inv ≫ e.hom.app X ▷ Y := rfl

/-- Maps in both tensor factors preserve the complete given representation and interchange. -/
@[reassoc]
theorem interchange_naturality (A : C) (S : C ⥤ C) (e : MonoidalCategory.tensorLeft A ≅ S)
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    S.map (f ⊗ₘ g) ≫ (interchange A S e X' Y').hom =
      (interchange A S e X Y).hom ≫ (S.map f ⊗ₘ g) := by
  have hE := e.inv.naturality (f ⊗ₘ g)
  have hF := e.hom.naturality f
  change (A ◁ f) ≫ e.hom.app X' = e.hom.app X ≫ S.map f at hF
  have hAssoc : A ◁ (f ⊗ₘ g) ≫ (α_ A X' Y').inv =
      (α_ A X Y).inv ≫ ((A ◁ f) ⊗ₘ g) := by
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 A) f g
  have hPair : ((A ◁ f) ⊗ₘ g) ≫ e.hom.app X' ▷ Y' =
      (e.hom.app X ▷ Y) ≫ (S.map f ⊗ₘ g) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hF]
  simp only [interchange_hom]
  calc
    _ = (e.inv.app (X ⊗ Y) ≫ A ◁ (f ⊗ₘ g)) ≫
        (α_ A X' Y').inv ≫ e.hom.app X' ▷ Y' := by
      rw [← Category.assoc, hE]
      rfl
    _ = e.inv.app (X ⊗ Y) ≫
        ((α_ A X Y).inv ≫ ((A ◁ f) ⊗ₘ g)) ≫ e.hom.app X' ▷ Y' := by
      rw [Category.assoc, ← Category.assoc (A ◁ (f ⊗ₘ g)), hAssoc]
    _ = e.inv.app (X ⊗ Y) ≫ (α_ A X Y).inv ≫
        (e.hom.app X ▷ Y) ≫ (S.map f ⊗ₘ g) := by
      simpa only [Category.assoc] using
        congrArg (fun k => e.inv.app (X ⊗ Y) ≫ (α_ A X Y).inv ≫ k) hPair
    _ = _ := by simp only [Category.assoc]

/-- The interchange is a natural isomorphism on every first-factor input. -/
def interchangeFunctorIso (A : C) (S : C ⥤ C) (e : MonoidalCategory.tensorLeft A ≅ S) (Y : C) :
    MonoidalCategory.tensorRight Y ⋙ S ≅ S ⋙ MonoidalCategory.tensorRight Y :=
  NatIso.ofComponents (fun X ↦ interchange A S e X Y) (by
    intro X X' f
    change S.map (f ▷ Y) ≫ (interchange A S e X' Y).hom =
      (interchange A S e X Y).hom ≫ S.map f ▷ Y
    simpa only [tensorHom_id] using interchange_naturality A S e f (𝟙 Y))

/-- A natural change in the representing object and represented functor preserves the full associator interchange. -/
theorem coefficient_naturality {A A' : C} {S S' : C ⥤ C}
    (p : A ⟶ A') (q : S ⟶ S')
    (e : MonoidalCategory.tensorLeft A ≅ S)
    (e' : MonoidalCategory.tensorLeft A' ≅ S')
    (h : ∀ X : C, (p ▷ X) ≫ e'.hom.app X = e.hom.app X ≫ q.app X)
    (X Y : C) :
    q.app (X ⊗ Y) ≫ (interchange A' S' e' X Y).hom =
      (interchange A S e X Y).hom ≫ (q.app X ▷ Y) := by
  have hInv : q.app (X ⊗ Y) ≫ e'.inv.app (X ⊗ Y) =
      e.inv.app (X ⊗ Y) ≫ (p ▷ (X ⊗ Y)) := by
    simpa only [Iso.app_inv] using
      (CommSq.vert_inv (g := e.app (X ⊗ Y)) (h := e'.app (X ⊗ Y)) ⟨h (X ⊗ Y)⟩).w
  have hAssoc : (p ▷ (X ⊗ Y)) ≫ (α_ A' X Y).inv =
      (α_ A X Y).inv ≫ ((p ▷ X) ▷ Y) :=
    associator_inv_naturality_left p X Y
  have hPair : ((p ▷ X) ▷ Y) ≫ (e'.hom.app X ▷ Y) =
      (e.hom.app X ▷ Y) ≫ (q.app X ▷ Y) := by
    simpa only [comp_whiskerRight] using congrArg (fun f => f ▷ Y) (h X)
  simp only [interchange_hom]
  calc
    _ = (e.inv.app (X ⊗ Y) ≫ (p ▷ (X ⊗ Y))) ≫
        (α_ A' X Y).inv ≫ (e'.hom.app X ▷ Y) := by
      rw [← Category.assoc, hInv]
    _ = e.inv.app (X ⊗ Y) ≫
        ((α_ A X Y).inv ≫ ((p ▷ X) ▷ Y)) ≫ (e'.hom.app X ▷ Y) := by
      rw [Category.assoc, ← Category.assoc (p ▷ (X ⊗ Y)), hAssoc]
    _ = e.inv.app (X ⊗ Y) ≫ (α_ A X Y).inv ≫
        (e.hom.app X ▷ Y) ≫ (q.app X ▷ Y) := by
      simpa only [Category.assoc] using
        congrArg (fun f => e.inv.app (X ⊗ Y) ≫ (α_ A X Y).inv ≫ f) hPair
    _ = _ := by simp only [Category.assoc]


end CategoryTheory.TensorRepresentedInterchange
