/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/Mod/Comap.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Restriction of scalars along an isomorphism of monoid objects

Mathlib's `Mod.comap f` restricts the scalars of internal modules along a morphism
`f : A ⟶ B` of monoid objects, acting by `f ⊵ₗ M ≫ γ[B, M]` on the same underlying object.
When `e : A ≅ B` is an isomorphism of monoid objects, restricting along `e.hom` and along
`e.inv` are mutually inverse, so `Mod.comapEquivalence e` identifies the categories of
`B`-modules and `A`-modules without changing underlying objects; the unit and counit are
given by identity morphisms of the underlying objects.

This is how a model of a monoid object that is isomorphic, but not equal, to a chosen one is
shown to have the same category of modules, for example a sphere monoid in symmetric sequences.
-/

public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonoidalLeftAction MonObj

namespace CategoryTheory.Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]
  {A B : C} [MonObj A] [MonObj B]

omit [MonObj A] in
/-- Restricting the scalars of a `B`-module along `f : A ⟶ B` and then along `g : B ⟶ A`, where
`g ≫ f = 𝟙 B`, recovers its action: the identity is equivariant in both directions. -/
private lemma smul_comp_id_eq (f : A ⟶ B) (g : B ⟶ A) (h : g ≫ f = 𝟙 B) (X : D) [ModObj B X] :
    γ[B, X] ≫ 𝟙 X = B ⊴ₗ 𝟙 X ≫ g ⊵ₗ X ≫ f ⊵ₗ X ≫ γ[B, X] ∧
      (g ⊵ₗ X ≫ f ⊵ₗ X ≫ γ[B, X]) ≫ 𝟙 X = B ⊴ₗ 𝟙 X ≫ γ[B, X] := by
  simp [← comp_actionHomLeft_assoc, h]

/-- A `B`-module is isomorphic, by its identity, to its restriction along `f : A ⟶ B` and then
along `g : B ⟶ A`, when `g ≫ f = 𝟙 B`. -/
def comapCompIso (f : A ⟶ B) (g : B ⟶ A) [IsMonHom f] [IsMonHom g] (h : g ≫ f = 𝟙 B)
    (M : Mod D B) : M ≅ (comap g).obj ((comap f).obj M) where
  hom := Hom.mk' (𝟙 M.X) (smul_comp_id_eq f g h M.X).1
  inv := Hom.mk' (𝟙 M.X) (smul_comp_id_eq f g h M.X).2
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

@[simp]
lemma comapCompIso_hom_hom (f : A ⟶ B) (g : B ⟶ A) [IsMonHom f] [IsMonHom g] (h : g ≫ f = 𝟙 B)
    (M : Mod D B) : (comapCompIso f g h M).hom.hom = 𝟙 M.X := (rfl)

@[simp]
lemma comapCompIso_inv_hom (f : A ⟶ B) (g : B ⟶ A) [IsMonHom f] [IsMonHom g] (h : g ≫ f = 𝟙 B)
    (M : Mod D B) : (comapCompIso f g h M).inv.hom = 𝟙 M.X := (rfl)

/-- Restriction of scalars along an isomorphism `e : A ≅ B` of monoid objects is an equivalence
between the categories of `B`-modules and of `A`-modules, with inverse the restriction along
`e.inv`. -/
@[expose] def comapEquivalence (e : A ≅ B) [IsMonHom e.hom] : Mod D B ≌ Mod D A where
  functor := comap e.hom
  inverse := comap e.inv
  unitIso := NatIso.ofComponents (comapCompIso e.hom e.inv e.inv_hom_id) fun _ ↦ by
    ext
    simp only [comp_hom', comapCompIso_hom_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  counitIso := (NatIso.ofComponents (comapCompIso e.inv e.hom e.hom_inv_id) fun _ ↦ by
    ext
    simp only [comp_hom', comapCompIso_hom_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm).symm
  functor_unitIso_comp _ := by
    ext
    simp only [NatIso.ofComponents_hom_app, Functor.id_obj, Functor.comp_obj, Iso.symm_hom,
      NatIso.ofComponents_inv_app, comp_hom', comap_map_hom, comapCompIso_hom_hom,
      comapCompIso_inv_hom, id_hom']
    exact Category.id_comp _

@[simp]
lemma comapEquivalence_functor (e : A ≅ B) [IsMonHom e.hom] :
    (comapEquivalence (D := D) e).functor = comap e.hom := (rfl)

@[simp]
lemma comapEquivalence_inverse (e : A ≅ B) [IsMonHom e.hom] :
    (comapEquivalence (D := D) e).inverse = comap e.inv := (rfl)

@[simp]
lemma comapEquivalence_unitIso_hom_app_hom (e : A ≅ B) [IsMonHom e.hom] (M : Mod D B) :
    ((comapEquivalence e).unitIso.hom.app M).hom = 𝟙 M.X := (rfl)

@[simp]
lemma comapEquivalence_unitIso_inv_app_hom (e : A ≅ B) [IsMonHom e.hom] (M : Mod D B) :
    ((comapEquivalence e).unitIso.inv.app M).hom = 𝟙 M.X := (rfl)

@[simp]
lemma comapEquivalence_counitIso_hom_app_hom (e : A ≅ B) [IsMonHom e.hom] (M : Mod D A) :
    ((comapEquivalence e).counitIso.hom.app M).hom = 𝟙 M.X := (rfl)

@[simp]
lemma comapEquivalence_counitIso_inv_app_hom (e : A ≅ B) [IsMonHom e.hom] (M : Mod D A) :
    ((comapEquivalence e).counitIso.inv.app M).hom = 𝟙 M.X := (rfl)

end CategoryTheory.Mod
