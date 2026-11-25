/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Effaceable and coeffaceable functors

A functor is effaceable when each object admits a monomorphism whose
image map is zero; coeffaceability uses an epimorphism instead. Vanishing
on injective or projective objects gives these properties through
presentations.

## References

* C. Weibel, *An Introduction to Homological Algebra* (1994), Exercise 2.4.5.
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

section Predicates

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B] [HasZeroMorphisms B]

namespace Functor

/-- A functor is effaceable if every object embeds into an object along a map
which the functor sends to zero. -/
def IsEffaceable (F : A ⥤ B) : Prop :=
  ∀ X : A, ∃ (I : A) (u : X ⟶ I), Mono u ∧ F.map u = 0

/-- A functor is coeffaceable if every object is the quotient of an object along
a map which the functor sends to zero. -/
def IsCoeffaceable (F : A ⥤ B) : Prop :=
  ∀ X : A, ∃ (P : A) (u : P ⟶ X), Epi u ∧ F.map u = 0

/-- A functor vanishing on injective objects can be effaced through native
injective presentations. Only the target needs zero morphisms. -/
theorem isEffaceable_of_isZero_obj_injective (F : A ⥤ B) [EnoughInjectives A]
    (hF : ∀ (I : A) [Injective I], IsZero (F.obj I)) : F.IsEffaceable := by
  intro X
  obtain ⟨I⟩ := EnoughInjectives.presentation X
  exact ⟨I.J, I.f, inferInstance, (hF I.J).eq_of_tgt _ _⟩

/-- A functor vanishing on projective objects can be coeffaced through native
projective presentations. Only the target needs zero morphisms. -/
theorem isCoeffaceable_of_isZero_obj_projective (F : A ⥤ B) [EnoughProjectives A]
    (hF : ∀ (P : A) [Projective P], IsZero (F.obj P)) : F.IsCoeffaceable := by
  intro X
  obtain ⟨P⟩ := EnoughProjectives.presentation X
  exact ⟨P.p, P.f, inferInstance, (hF P.p).eq_of_src _ _⟩

end Functor

end Predicates

end CategoryTheory
