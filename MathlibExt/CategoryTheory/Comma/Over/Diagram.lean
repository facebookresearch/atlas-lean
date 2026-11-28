/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Diagrams in a slice category

For categories `J,C` and `A : C`, an augmented diagram is a functor `P : J → C` with a natural
transformation `η_P : P → const(A)`. Its lift is the diagram in `Over A` with component
`η_P(j) : P(j) → A`.

A natural transformation `θ : P → Q` with `η_Q ∘ θ=η_P` gives component maps in the slice.
This defines a functor from the slice of the functor category over `const(A)` to `J → Over A`.

Reference: Mac Lane, *Categories for the Working Mathematician*, Chapter II.
-/

@[expose] public section

open CategoryTheory

universe uJ vJ uC vC

namespace CategoryTheory.Over

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C] (A : C)

/-- Let `J,C` be categories, `A : C`, and `P,Q` be functors `J → C` with augmentations `η_P,η_Q`
to the constant diagram at `A`. A natural transformation `θ : P → Q` satisfying `η_Q ∘ θ=η_P`
induces a natural map between their `Over A` diagrams, with component the slice morphism
underlying `θ_j : P_j → Q_j`. -/
def liftDiagramMap {P Q : Over ((Functor.const J).obj A)} (f : P ⟶ Q) :
    Over.lift P.left P.hom ⟶ Over.lift Q.left Q.hom where
  app j := Over.homMk (f.left.app j) (NatTrans.congr_app f.w j)
  naturality {i j} g := by
    apply Over.OverMorphism.ext
    exact f.left.naturality g

@[simp]
theorem liftDiagramMap_id (P : Over ((Functor.const J).obj A)) :
    liftDiagramMap A (𝟙 P) = 𝟙 (Over.lift P.left P.hom) := by
  ext j
  rfl

theorem liftDiagramMap_comp {P Q T : Over ((Functor.const J).obj A)}
    (f : P ⟶ Q) (g : Q ⟶ T) :
    liftDiagramMap A (f ≫ g) = liftDiagramMap A f ≫ liftDiagramMap A g := by
  ext j
  rfl

/-- For categories `J,C` and `A : C`, `liftDiagramFunctor A : Over(const_J A) → (J → Over A)`
sends an augmented diagram `P → const_J A` to its componentwise slice diagram. A morphism is
sent componentwise to the commuting triangle over `A`. -/
def liftDiagramFunctor : Over ((Functor.const J).obj A) ⥤ (J ⥤ Over A) where
  obj P := Over.lift P.left P.hom
  map := liftDiagramMap A
  map_id := liftDiagramMap_id A
  map_comp := liftDiagramMap_comp A

end CategoryTheory.Over

end
