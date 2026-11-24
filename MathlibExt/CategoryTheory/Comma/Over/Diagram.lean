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

A diagram with a natural transformation to the constant diagram at `A`
induces a diagram in `Over A`. Morphisms of augmented diagrams lift to
morphisms of the slice diagrams. These constructions are functorial for
arbitrary diagram categories and independent object and morphism universes.
-/

@[expose] public section

open CategoryTheory

universe uJ vJ uC vC

namespace CategoryTheory.Over

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C] (A : C)

/-- The original augmented-diagram components as actual maps in the slice. -/
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

/-- Native slice lifting is a functor on actual augmented diagrams. -/
def liftDiagramFunctor : Over ((Functor.const J).obj A) ⥤ (J ⥤ Over A) where
  obj P := Over.lift P.left P.hom
  map := liftDiagramMap A
  map_id := liftDiagramMap_id A
  map_comp := liftDiagramMap_comp A

end CategoryTheory.Over

end
