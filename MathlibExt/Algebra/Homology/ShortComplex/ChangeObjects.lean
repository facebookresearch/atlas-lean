/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Changing short-complex objects by isomorphisms

In a category with zero morphisms, a short complex S₁ → S₂ → S₃ can be written in any specified
isomorphic coordinates A → B → D. For coordinate isomorphisms eᵢ, the arrows become e₂ ∘ f ∘
e₁⁻¹ and e₃ ∘ g ∘ e₂⁻¹. The three isomorphisms form an isomorphism of short complexes.

Exactness and short exactness are preserved in both directions. Morphisms are conjugated
componentwise, and the coordinate construction satisfies identity, composition and naturality
laws.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Category Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (S : ShortComplex C) {A B D : C}

/-- Let C be a category with zero morphisms, and let S=(S₁ → S₂ → S₃) be a short complex with arrows
f,g and g ∘ f=0. Specify isomorphisms e₁ : S₁ ≅ A, e₂ : S₂ ≅ B and e₃ : S₃ ≅ D. The short
complex A → B → D has arrows e₂ ∘ f ∘ e₁⁻¹ and e₃ ∘ g ∘ e₂⁻¹. Their composite is zero, and the
original and changed complexes are isomorphic. -/
def changeObjects (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    ShortComplex C :=
  ShortComplex.mk (e₁.inv ≫ S.f ≫ e₂.hom) (e₂.inv ≫ S.g ≫ e₃.hom) (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc S.f S.g e₃.hom, S.zero, zero_comp, comp_zero])

/-- Let C be a category with zero morphisms, and let S=(S₁ → S₂ → S₃) be a short complex with arrows
f,g and g ∘ f=0. Specify isomorphisms e₁ : S₁ ≅ A, e₂ : S₂ ≅ B and e₃ : S₃ ≅ D. The first arrow
of the changed complex A → B → D is e₂ ∘ f ∘ e₁⁻¹ : A → B. -/
@[simp]
lemma changeObjects_f (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    (S.changeObjects e₁ e₂ e₃).f = e₁.inv ≫ S.f ≫ e₂.hom := rfl

/-- Let C be a category with zero morphisms, and let S=(S₁ → S₂ → S₃) be a short complex with arrows
f,g and g ∘ f=0. Specify isomorphisms e₁ : S₁ ≅ A, e₂ : S₂ ≅ B and e₃ : S₃ ≅ D. The second arrow
of the changed complex is e₃ ∘ g ∘ e₂⁻¹ : B → D. -/
@[simp]
lemma changeObjects_g (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    (S.changeObjects e₁ e₂ e₃).g = e₂.inv ≫ S.g ≫ e₃.hom := rfl

/-- Let C be a category with zero morphisms, and let S=(S₁ → S₂ → S₃) be a short complex with arrows
f,g and g ∘ f=0. Specify isomorphisms e₁ : S₁ ≅ A, e₂ : S₂ ≅ B and e₃ : S₃ ≅ D. The original
short complex is canonically isomorphic to the changed complex A → B → D, with components
e₁,e₂,e₃. -/
def changeObjectsIso (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    S ≅ S.changeObjects e₁ e₂ e₃ :=
  ShortComplex.isoMk e₁ e₂ e₃
    (by
      change e₁.hom ≫ (e₁.inv ≫ S.f ≫ e₂.hom) = S.f ≫ e₂.hom
      exact e₁.hom_inv_id_assoc (S.f ≫ e₂.hom))
    (by
      change e₂.hom ≫ (e₂.inv ≫ S.g ≫ e₃.hom) = S.g ≫ e₃.hom
      exact e₂.hom_inv_id_assoc (S.g ≫ e₃.hom))

/-- Let C be a category with zero morphisms, and let S=(S₁ → S₂ → S₃) be a short complex with arrows
f,g and g ∘ f=0. Specify isomorphisms e₁ : S₁ ≅ A, e₂ : S₂ ≅ B and e₃ : S₃ ≅ D. The changed
short complex is exact if and only if S is exact. Exactness is transported through the specified
three-component isomorphism. -/
lemma changeObjects_exact_iff (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    (S.changeObjects e₁ e₂ e₃).Exact ↔ S.Exact :=
  (exact_iff_of_iso (S.changeObjectsIso e₁ e₂ e₃)).symm

/-- Let C be a category with zero morphisms, and let S=(S₁ → S₂ → S₃) be a short complex with arrows
f,g and g ∘ f=0. Specify isomorphisms e₁ : S₁ ≅ A, e₂ : S₂ ≅ B and e₃ : S₃ ≅ D. The changed
complex A → B → D is short exact if and only if S is short exact: the coordinate isomorphism
preserves exactness, the monomorphism of the first arrow and the epimorphism of the second. -/
lemma changeObjects_shortExact_iff
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    (S.changeObjects e₁ e₂ e₃).ShortExact ↔ S.ShortExact :=
  (shortExact_iff_of_iso (S.changeObjectsIso e₁ e₂ e₃)).symm

variable {S} {T U : ShortComplex C} {A' B' D' A'' B'' D'' : C}

/-- Let C have zero morphisms, φ : S → T be a morphism of short complexes, and eᵢ : Sᵢ ≅ Aᵢ and e′ᵢ
: Tᵢ ≅ A′ᵢ be specified coordinate isomorphisms for i=1,2,3. The changed short complexes form a
morphism with components e′ᵢ ∘ φᵢ ∘ eᵢ⁻¹. Its two squares commute because those of φ commute. -/
def changeObjectsMap (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    S.changeObjects e₁ e₂ e₃ ⟶ T.changeObjects e₁' e₂' e₃' :=
  (S.changeObjectsIso e₁ e₂ e₃).inv ≫ φ ≫ (T.changeObjectsIso e₁' e₂' e₃').hom

/-- Let C have zero morphisms, φ : S → T be a morphism of short complexes, and eᵢ : Sᵢ ≅ Aᵢ and e′ᵢ
: Tᵢ ≅ A′ᵢ be specified coordinate isomorphisms for i=1,2,3. The first component A₁ → A′₁ of the
induced coordinate map is e′₁ ∘ φ₁ ∘ e₁⁻¹. -/
@[simp]
lemma changeObjectsMap_τ₁ (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    (changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃').τ₁ =
      e₁.inv ≫ φ.τ₁ ≫ e₁'.hom := rfl

/-- Let C have zero morphisms, φ : S → T be a morphism of short complexes, and eᵢ : Sᵢ ≅ Aᵢ and e′ᵢ
: Tᵢ ≅ A′ᵢ be specified coordinate isomorphisms for i=1,2,3. The middle component A₂ → A′₂ of
the induced coordinate map is e′₂ ∘ φ₂ ∘ e₂⁻¹. -/
@[simp]
lemma changeObjectsMap_τ₂ (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    (changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃').τ₂ =
      e₂.inv ≫ φ.τ₂ ≫ e₂'.hom := rfl

/-- Let C have zero morphisms, φ : S → T be a morphism of short complexes, and eᵢ : Sᵢ ≅ Aᵢ and e′ᵢ
: Tᵢ ≅ A′ᵢ be specified coordinate isomorphisms for i=1,2,3. The last component A₃ → A′₃ of the
induced coordinate map is e′₃ ∘ φ₃ ∘ e₃⁻¹. -/
@[simp]
lemma changeObjectsMap_τ₃ (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    (changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃').τ₃ =
      e₃.inv ≫ φ.τ₃ ≫ e₃'.hom := rfl

/-- Let C have zero morphisms, φ : S → T be a morphism of short complexes, and eᵢ : Sᵢ ≅ Aᵢ and e′ᵢ
: Tᵢ ≅ A′ᵢ be specified coordinate isomorphisms for i=1,2,3. If E_S and E_T are the coordinate
isomorphisms and φ′ is the induced changed-coordinate map, then E_T ∘ φ = φ′ ∘ E_S. -/
@[reassoc]
lemma changeObjectsIso_hom_naturality (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    φ ≫ (T.changeObjectsIso e₁' e₂' e₃').hom =
      (S.changeObjectsIso e₁ e₂ e₃).hom ≫
        changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃' := by
  simp only [changeObjectsMap, Iso.hom_inv_id_assoc]

/-- Let C have zero morphisms, φ : S → T be a morphism of short complexes, and eᵢ : Sᵢ ≅ Aᵢ and e′ᵢ
: Tᵢ ≅ A′ᵢ be specified coordinate isomorphisms for i=1,2,3. The inverse coordinate isomorphisms
satisfy E_T⁻¹ ∘ φ′ = φ ∘ E_S⁻¹, where φ′ is the changed-coordinate map. -/
@[reassoc]
lemma changeObjectsIso_inv_naturality (φ : S ⟶ T)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D') :
    changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃' ≫
        (T.changeObjectsIso e₁' e₂' e₃').inv =
      (S.changeObjectsIso e₁ e₂ e₃).inv ≫ φ := by
  simp only [changeObjectsMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Let C be a category with zero morphisms, and let S=(S₁ → S₂ → S₃) be a short complex with arrows
f,g and g ∘ f=0. Specify isomorphisms e₁ : S₁ ≅ A, e₂ : S₂ ≅ B and e₃ : S₃ ≅ D. Changing the
identity morphism of S by these same coordinate isomorphisms gives the identity morphism of A →
B → D. -/
@[simp]
lemma changeObjectsMap_id
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D) :
    changeObjectsMap (𝟙 S) e₁ e₂ e₃ e₁ e₂ e₃ = 𝟙 _ := by
  simp only [changeObjectsMap, Category.id_comp, Iso.inv_hom_id]

/-- Let C have zero morphisms, φ : S → T and ψ : T → U be short-complex maps, and specify coordinate
isomorphisms for all three complexes. The coordinate map of ψ ∘ φ is the composite of the
coordinate map of φ followed by that of ψ. -/
lemma changeObjectsMap_comp (φ : S ⟶ T) (ψ : T ⟶ U)
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (e₁' : T.X₁ ≅ A') (e₂' : T.X₂ ≅ B') (e₃' : T.X₃ ≅ D')
    (e₁'' : U.X₁ ≅ A'') (e₂'' : U.X₂ ≅ B'') (e₃'' : U.X₃ ≅ D'') :
    changeObjectsMap (φ ≫ ψ) e₁ e₂ e₃ e₁'' e₂'' e₃'' =
      changeObjectsMap φ e₁ e₂ e₃ e₁' e₂' e₃' ≫
        changeObjectsMap ψ e₁' e₂' e₃' e₁'' e₂'' e₃'' := by
  simp only [changeObjectsMap, Category.assoc, Iso.hom_inv_id_assoc]

end CategoryTheory.ShortComplex
