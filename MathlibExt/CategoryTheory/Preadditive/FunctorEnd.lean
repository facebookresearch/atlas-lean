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
# Endomorphism rings under additive and linear functors

An additive functor `F : C ⥤ D` between preadditive categories induces a ring homomorphism
`End(X) → End(F(X))`, with underlying map `a ↦ F.map(a)`. Identity and composite functors
induce the identity and composite ring homomorphisms.

If the categories are linear over a commutative semiring `R` and `F` is `R`-linear, this map
is an `R`-algebra homomorphism. The category-object, morphism, and scalar universes are
independent.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃ w

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E]

/-- The endomorphism-ring homomorphism of an additive functor.

For an object `X`, an additive functor sends each endomorphism to its functorial image,
preserving ring addition, multiplication, zero, and identity. -/
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

/-- The carrier morphism of an additive endomorphism-ring map.

The endomorphism-ring homomorphism induced by `F` has underlying morphism `F.map(a.asHom)` at
`a ∈ End(X)`. -/
@[simp]
theorem mapEndRingHom_asHom (F : C ⥤ D) [F.Additive] (X : C) (a : End X) :
    (F.mapEndRingHom X a).asHom = F.map a.asHom := rfl

/-- Composition of additive endomorphism-ring maps.

The ring homomorphism induced by `F ⋙ G` is the map induced by `F` followed by that induced by
`G` at `F(X)`. -/
theorem mapEndRingHom_comp (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] (X : C) :
    (F ⋙ G).mapEndRingHom X = (G.mapEndRingHom (F.obj X)).comp (F.mapEndRingHom X) := by
  apply RingHom.ext
  intro a
  apply End.ext
  rfl

/-- The identity endomorphism-ring homomorphism of the identity functor.

The identity functor induces the identity ring homomorphism on each endomorphism ring. -/
@[simp]
theorem mapEndRingHom_id (X : C) : (𝟭 C).mapEndRingHom X = RingHom.id (End X) := by
  apply RingHom.ext
  intro a
  apply End.ext
  rfl

variable (R : Type w) [CommSemiring R]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [CategoryTheory.Linear R E]

/-- The endomorphism-algebra homomorphism of a linear functor.

For categories linear over a commutative semiring `R`, an additive `R`-linear functor induces
an `R`-algebra homomorphism `End(X) → End(F(X))`. -/
def mapEndAlgHom (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C) :
    End X →ₐ[R] End (F.obj X) :=
  { F.mapEndRingHom X with
    commutes' := by
      intro r
      apply End.ext
      simp only [Algebra.algebraMap_eq_smul_one]
      change F.map (r • 𝟙 X) = r • 𝟙 (F.obj X)
      rw [F.map_smul, F.map_id] }

/-- The carrier morphism of a linear endomorphism-algebra map.

The scalar-algebra homomorphism induced by `F` has underlying morphism `F.map(a.asHom)`. -/
@[simp]
theorem mapEndAlgHom_asHom (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C) (a : End X) :
    (F.mapEndAlgHom R X a).asHom = F.map a.asHom := rfl

/-- Composition of linear endomorphism-algebra maps.

The algebra homomorphism induced by `F ⋙ G` is the composite of the algebra homomorphisms
induced by `F` and `G`. -/
theorem mapEndAlgHom_comp (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ E) [G.Additive] [G.Linear R] (X : C) :
    (F ⋙ G).mapEndAlgHom R X =
      (G.mapEndAlgHom R (F.obj X)).comp (F.mapEndAlgHom R X) := by
  apply AlgHom.ext
  intro a
  apply End.ext
  rfl

end CategoryTheory.Functor
