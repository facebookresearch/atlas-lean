/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Author: @toskua, Avocado

Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @junekim623, Muse

Provenance: conjugation naturality is relocated from
MathlibExt/CategoryTheory/Abelian/RightDerived/LongExact.lean.
It retains the original Hartshorne sheaf-Ext formalization credits.
-/
module

public import Mathlib.CategoryTheory.CommSq

/-!
# Naturality under comparison isomorphisms

In a category, a commuting square remains commuting after both endpoints
are identified by compatible isomorphisms. Equality of isomorphisms after
identifying equal endpoint objects is determined by equality of their forward maps.
-/

@[expose] public section

namespace CategoryTheory.Iso

/-- In a category `E`, take compatible endpoint isomorphisms
`eᵢ : Aᵢ ≅ Hᵢ`, `tᵢ : Bᵢ ≅ Kᵢ`, maps `dᵢ : Hᵢ → Kᵢ`,
and maps `f`, `g`, `a`, `b` between the respective endpoints. If
`f ≫ e₁ = e₂ ≫ a`, `b ≫ t₁⁻¹ = t₂⁻¹ ≫ g`, and
`d₂ ≫ b = a ≫ d₁`, the transported maps satisfy
`(e₂ ≫ d₂ ≫ t₂⁻¹) ≫ g = f ≫ (e₁ ≫ d₁ ≫ t₁⁻¹)`. -/
lemma conjugate_naturality {E : Type*} [Category E]
    {A₁ A₂ B₁ B₂ H₁ H₂ K₁ K₂ : E}
    (e₁ : A₁ ≅ H₁) (e₂ : A₂ ≅ H₂) (t₁ : B₁ ≅ K₁) (t₂ : B₂ ≅ K₂)
    (d₁ : H₁ ⟶ K₁) (d₂ : H₂ ⟶ K₂)
    (f : A₂ ⟶ A₁) (g : B₂ ⟶ B₁) (a : H₂ ⟶ H₁) (b : K₂ ⟶ K₁)
    (hsource : f ≫ e₁.hom = e₂.hom ≫ a)
    (htarget : b ≫ t₁.inv = t₂.inv ≫ g)
    (hnatural : d₂ ≫ b = a ≫ d₁) :
    (e₂.hom ≫ d₂ ≫ t₂.inv) ≫ g = f ≫ (e₁.hom ≫ d₁ ≫ t₁.inv) := by
  have s₁ : CommSq e₂.hom f a e₁.hom := ⟨hsource.symm⟩
  have s₂ : CommSq d₂ a b d₁ := ⟨hnatural⟩
  have s₃ : CommSq t₂.inv b g t₁.inv := ⟨htarget.symm⟩
  simpa only [Category.assoc] using ((s₁.horiz_comp s₂).horiz_comp s₃).w

end CategoryTheory.Iso

namespace CategoryTheory

/-!
# Equality of isomorphisms with identified endpoints

In a category, identify `X` with `X′` and `Y` with `Y′` by object
equalities. Equality of isomorphisms between these endpoints implies
equality of their forward and inverse maps; equality of their forward
maps determines equality of the isomorphisms.
-/

/-- In a category `C`, suppose `X = X′`, `Y = Y′`, and the
isomorphisms `I : X ≅ Y`, `J : X′ ≅ Y′` agree after these
endpoint identifications. Their forward maps also agree under the same identifications. -/
theorem heq_iso_hom {C : Type*} [Category C] {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {I : X ≅ Y} {J : X' ≅ Y'} (h : HEq I J) : HEq I.hom J.hom := by
  subst hX; subst hY; rw [eq_of_heq h]

/- Proof implementation note.
From an `HEq` of their `hom`s, an `HEq` of the isomorphisms themselves.
Generic hom-`HEq` to `Iso`-`HEq` constructor.
-/

/-- In a category `C`, suppose `X = X′` and `Y = Y′`. If the
forward maps of `I : X ≅ Y` and `J : X′ ≅ Y′` agree under
these identifications, the isomorphisms themselves agree under them. -/
theorem heq_iso_of_hom {C : Type*} [Category C] {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {I : X ≅ Y} {J : X' ≅ Y'} (h : HEq I.hom J.hom) : HEq I J := by
  subst hX; subst hY; exact heq_of_eq (Iso.ext (eq_of_heq h))

/-- In a category `C`, suppose `X = X′`, `Y = Y′`, and
`I : X ≅ Y`, `J : X′ ≅ Y′` agree under these endpoint
identifications. Their inverse maps `Y → X` and `Y′ → X′`
agree under the corresponding identifications. -/
theorem heq_iso_inv {C : Type*} [Category C] {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {I : X ≅ Y} {J : X' ≅ Y'} (h : HEq I J) : HEq I.inv J.inv := by
  subst hX; subst hY; rw [eq_of_heq h]

end CategoryTheory
