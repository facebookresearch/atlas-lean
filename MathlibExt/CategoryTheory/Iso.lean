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
# Naturality through endpoint isomorphisms

Commutative squares paste horizontally to give naturality after conjugating morphisms by
isomorphisms at their endpoints.
-/

@[expose] public section

namespace CategoryTheory.Iso

/-- Naturality is preserved when both ends of a morphism are transported by isomorphisms. -/
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
# Naturality through endpoint isomorphisms

Commutative squares paste horizontally to give naturality after conjugating morphisms by
isomorphisms at their endpoints.
-/

/-- From an `HEq` of isomorphisms over equal endpoints, an `HEq` of their `hom`s. -/
theorem heq_iso_hom {C : Type*} [Category C] {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {I : X ≅ Y} {J : X' ≅ Y'} (h : HEq I J) : HEq I.hom J.hom := by
  subst hX; subst hY; rw [eq_of_heq h]

/-- From an `HEq` of their `hom`s, an `HEq` of the isomorphisms themselves.
Generic hom-`HEq` to `Iso`-`HEq` constructor. -/
theorem heq_iso_of_hom {C : Type*} [Category C] {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {I : X ≅ Y} {J : X' ≅ Y'} (h : HEq I.hom J.hom) : HEq I J := by
  subst hX; subst hY; exact heq_of_eq (Iso.ext (eq_of_heq h))

/-- From an `HEq` of isomorphisms over equal endpoints, an `HEq` of their `inv`s.
The `.inv` companion of `heq_iso_hom`. -/
theorem heq_iso_inv {C : Type*} [Category C] {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {I : X ≅ Y} {J : X' ≅ Y'} (h : HEq I J) : HEq I.inv J.inv := by
  subst hX; subst hY; rw [eq_of_heq h]

end CategoryTheory
