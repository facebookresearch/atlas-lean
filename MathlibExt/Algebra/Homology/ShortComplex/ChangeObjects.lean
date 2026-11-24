/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Changing the objects of a short complex by specified isomorphisms

The arrows are the conjugates of the original arrows. Their composite is
zero, and the original complex has a canonical isomorphism to the resulting
complex. Only a category with zero morphisms is needed.

The construction centralizes the object-coordinate changes used by universal
coefficient sequences. Exactness is transported by the native short-complex
isomorphism API; it is not an extra input to the construction.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Category Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (S : ShortComplex C) {A B D : C}

/-- Conjugate the two original arrows by the three specified object isomorphisms. -/
def changeObjects (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    ShortComplex C :=
  ShortComplex.mk (e₁.inv ≫ S.f ≫ e₂.hom) (e₂.inv ≫ S.g ≫ e₃.hom) (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc S.f S.g e₃.hom, S.zero, zero_comp, comp_zero])

/-- The first arrow is the conjugate of the actual original first arrow. -/
@[simp]
lemma changeObjects_f (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    (S.changeObjects e₁ e₂ e₃).f = e₁.inv ≫ S.f ≫ e₂.hom := rfl

/-- The second arrow is the conjugate of the actual original second arrow. -/
@[simp]
lemma changeObjects_g (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    (S.changeObjects e₁ e₂ e₃).g = e₂.inv ≫ S.g ≫ e₃.hom := rfl

/-- The original complex is canonically isomorphic to its specified coordinates. -/
def changeObjectsIso (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    S ≅ S.changeObjects e₁ e₂ e₃ :=
  ShortComplex.isoMk e₁ e₂ e₃
    (by
      change e₁.hom ≫ (e₁.inv ≫ S.f ≫ e₂.hom) = S.f ≫ e₂.hom
      exact e₁.hom_inv_id_assoc (S.f ≫ e₂.hom))
    (by
      change e₂.hom ≫ (e₂.inv ≫ S.g ≫ e₃.hom) = S.g ≫ e₃.hom
      exact e₂.hom_inv_id_assoc (S.g ≫ e₃.hom))

/-- The native comparison preserves exactness in either direction. -/
lemma changeObjects_exact_iff (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    (S.changeObjects e₁ e₂ e₃).Exact ↔ S.Exact :=
  (exact_iff_of_iso (S.changeObjectsIso e₁ e₂ e₃)).symm

/-- The native comparison preserves all three short-exact conditions. -/
lemma changeObjects_shortExact_iff
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    (S.changeObjects e₁ e₂ e₃).ShortExact ↔ S.ShortExact :=
  (shortExact_iff_of_iso (S.changeObjectsIso e₁ e₂ e₃)).symm

variable {S} {T U : ShortComplex C} {A' B' D' A'' B'' D'' : C}

/-- An original complex morphism acts on both sets of actual object coordinates. -/
def changeObjectsMap (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    S.changeObjects e₁ e₂ e₃ ⟶ T.changeObjects e₁' e₂' e₃' :=
  (S.changeObjectsIso e₁ e₂ e₃).inv ≫ φ ≫ (T.changeObjectsIso e₁' e₂' e₃').hom

/-- The first coordinate is the original first component conjugated by its object maps. -/
@[simp]
lemma changeObjectsMap_τ₁ (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    (changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃').τ₁ =
      e₁.inv ≫ φ.τ₁ ≫ e₁'.hom := rfl

/-- The middle coordinate is the original middle component conjugated by its object maps. -/
@[simp]
lemma changeObjectsMap_τ₂ (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    (changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃').τ₂ =
      e₂.inv ≫ φ.τ₂ ≫ e₂'.hom := rfl

/-- The last coordinate is the original last component conjugated by its object maps. -/
@[simp]
lemma changeObjectsMap_τ₃ (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    (changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃').τ₃ =
      e₃.inv ≫ φ.τ₃ ≫ e₃'.hom := rfl

/-- The forward coordinate comparison is natural for the original complex morphism. -/
@[reassoc]
lemma changeObjectsIso_hom_naturality (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    φ ≫ (T.changeObjectsIso e₁' e₂' e₃').hom =
      (S.changeObjectsIso e₁ e₂ e₃).hom ≫
        changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃' := by
  simp only [changeObjectsMap, Iso.hom_inv_id_assoc]

/-- The inverse coordinate comparison is natural without cancellation by the client. -/
@[reassoc]
lemma changeObjectsIso_inv_naturality (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃' ≫
        (T.changeObjectsIso e₁' e₂' e₃').inv =
      (S.changeObjectsIso e₁ e₂ e₃).inv ≫ φ := by
  simp only [changeObjectsMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Identity acts identically after the specified coordinate change. -/
@[simp]
lemma changeObjectsMap_id
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    changeObjectsMap (𝟙 S) e₁ e₂ e₃ e₁ e₂ e₃ = 𝟙 _ := by
  simp only [changeObjectsMap, Category.id_comp, Iso.inv_hom_id]

/-- Coordinate changes preserve the composition of the original complex morphisms. -/
lemma changeObjectsMap_comp (φ : S ⟶ T) (ψ : T ⟶ U)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D')
    (e₁'' : U.X₁ ≅ A'') (e₂'' : U.X₂ ≅ B'') (e₃'' : U.X₃ ≅ D'') :
    changeObjectsMap (φ ≫ ψ) e₁ e₂ e₃ e₁'' e₂'' e₃'' =
      changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃' ≫
        changeObjectsMap ψ e₁' e₂' e₃' e₁'' e₂'' e₃'' := by
  simp only [changeObjectsMap, Category.assoc, Iso.hom_inv_id_assoc]

end CategoryTheory.ShortComplex
