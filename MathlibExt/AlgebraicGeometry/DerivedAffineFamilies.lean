/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The actual category of all simplicial affine families

An object is an algebra A, a simplex degree and a simplex of X(A).
An arrow contains the actual algebra map and the actual simplex map
carrying that simplex to the specified target simplex. This is exactly
the native category of elements of the uncurried prestack, with no
restriction to vertices or to invertible arrows.

The projection to algebras and reindexing by a prestack map are native
functors. They provide the shared index for categorical QCoh/Perf
descent and for graded mixed de Rham and closed-form diagrams.

References: PTVV, arXiv:1111.3209v4, §1; Toën--Vezzosi, HAG II,
Part 2. Category of elements and currying are completed Mathlib operations.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedAffineFamilies

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping

universe u

variable {k : Type u} [CommRing k]

/-- The actual affine-algebra/simplex type-valued functor. -/
def uncurried (X : Prestack k) : (SAlg k × SimplexCategoryᵒᵖ) ⥤ Type (u + 1) :=
  Functor.uncurry.obj X

/-- Every affine family simplex and every actual algebra/simplex morphism. -/
abbrev Families (X : Prestack k) := (uncurried X).Elements

/-- The literal underlying algebra of an affine family simplex. -/
def algebraProjection (X : Prestack k) : Families X ⥤ SAlg k :=
  Functor.Elements.π (uncurried X) ⋙ _root_.CategoryTheory.Prod.fst _ _

/-- The actual family represented by a specified simplex. -/
def family (X : Prestack k) (A : SAlg k) (n : SimplexCategoryᵒᵖ)
    (x : (X.obj A).obj n) : Families X :=
  (uncurried X).elementsMk (A, n) x

/-- Prestack maps induce their literal functor on all family simplices. -/
def reindex {X Y : Prestack k} (f : X ⟶ Y) : Families X ⥤ Families Y :=
  (Functor.uncurry.map f).mapElements

/-- Reindexing retains the actual algebra and every algebra map. -/
theorem reindex_algebra {X Y : Prestack k} (f : X ⟶ Y) :
    reindex f ⋙ algebraProjection Y = algebraProjection X := rfl

end MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
