/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Algebra.Hom

/-!
# Functorial endomorphism rings and scalar algebras

The native functor map on endomorphism monoids is a ring morphism for an
additive functor and a scalar algebra morphism for a linear functor. The
construction retains the native function on morphisms and independent
category, morphism and scalar universes.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃ w

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E]

/-- Additive functors send the native endomorphism ring to the native endomorphism ring. -/
def mapEndRingHom (F : C ⥤ D) [F.Additive] (X : C) : End X →+* End (F.obj X) :=
  { F.mapEnd (X := X) with
    map_zero' := by
      apply End.ext
      change F.map (0 : X ⟶ X) = 0
      exact F.map_zero X X
    map_add' := by
      intro a b
      apply End.ext
      change F.map (a.asHom + b.asHom) = F.map a.asHom + F.map b.asHom
      exact F.map_add }

/-- The endomorphism ring morphism uses precisely the original native functor map. -/
@[simp]
theorem mapEndRingHom_asHom (F : C ⥤ D) [F.Additive] (X : C) (a : End X) :
    (F.mapEndRingHom X a).asHom = F.map a.asHom := rfl

/-- Endomorphism-ring transport respects functor composition. -/
theorem mapEndRingHom_comp (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] (X : C) :
    (F ⋙ G).mapEndRingHom X = (G.mapEndRingHom (F.obj X)).comp (F.mapEndRingHom X) := by
  apply RingHom.ext
  intro a
  apply End.ext
  rfl

/-- The identity functor induces the identity endomorphism-ring morphism. -/
@[simp]
theorem mapEndRingHom_id (X : C) : (𝟭 C).mapEndRingHom X = RingHom.id (End X) := by
  apply RingHom.ext
  intro a
  apply End.ext
  rfl

variable (R : Type w) [CommSemiring R]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [CategoryTheory.Linear R E]

/-- Linear functors preserve the native scalar algebra on each endomorphism ring. -/
def mapEndAlgHom (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C) :
    End X →ₐ[R] End (F.obj X) :=
  { F.mapEndRingHom X with
    commutes' := by
      intro r
      apply End.ext
      simp only [Algebra.algebraMap_eq_smul_one]
      change F.map (r • 𝟙 X) = r • 𝟙 (F.obj X)
      rw [F.map_smul, F.map_id] }

@[simp]
theorem mapEndAlgHom_asHom (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C) (a : End X) :
    (F.mapEndAlgHom R X a).asHom = F.map a.asHom := rfl

/-- Scalar-algebra transport respects functor composition. -/
theorem mapEndAlgHom_comp (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ E) [G.Additive] [G.Linear R] (X : C) :
    (F ⋙ G).mapEndAlgHom R X =
      (G.mapEndAlgHom R (F.obj X)).comp (F.mapEndAlgHom R X) := by
  apply AlgHom.ext
  intro a
  apply End.ext
  rfl

end CategoryTheory.Functor
