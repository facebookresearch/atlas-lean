/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal

@[expose] public section

/-!
# Canonical simplicial-diagonal consumer tests

Minimal generic checks for `SSet.simplicialDiagonalFunctor`: object evaluation,
natural-transformation component evaluation, and the canonical diagonal of a
constant simplicial object.

Identity and composition restatements are intentionally omitted: they are
tautological functor laws already covered by the functor instance.

Nonclaims: no realization, weak equivalence, additivity, `π₀`, spectra, or Q/S
comparison.
-/

set_option autoImplicit false

open CategoryTheory Simplicial
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SimplicialDiagonalTests

universe u

/-- Degree-`a` object is the `a`-simplices of the level-`a` set. -/
example (X : SimplicialObject SSet.{u}) (a : SimplexCategoryᵒᵖ) :
    (SSet.simplicialDiagonalFunctor.obj X).obj a = (X.obj a).obj a := rfl

/-- Diagonal component is the diagonal of the level components. -/
example {X Y : SimplicialObject SSet.{u}} (α : X ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    (SSet.simplicialDiagonalFunctor.map α).app a = (α.app a).app a := rfl

/-- Diagonal object map is the inner map followed by the outer component. -/
example (X : SimplicialObject SSet.{u}) {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (SSet.simplicialDiagonalFunctor.obj X).map f =
      ↾fun x => (X.map f).app b ((X.obj a).map f x) :=
  SSet.simplicialDiagonalFunctor_obj_map X f

/-- The constant diagonal has the original degreewise carrier. -/
example (Z : SSet.{u}) (a : SimplexCategoryᵒᵖ) :
    (SSet.simplicialDiagonalFunctor.obj
      ((SimplicialObject.const SSet.{u}).obj Z)).obj a = Z.obj a :=
  rfl

/-- The constant diagonal retains the original simplicial structure map. -/
example (Z : SSet.{u}) {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (SSet.simplicialDiagonalFunctor.obj
      ((SimplicialObject.const SSet.{u}).obj Z)).map f = Z.map f := by
  rw [SSet.simplicialDiagonalFunctor_obj_map]
  rfl

/-- Both components of the canonical constant-diagonal isomorphism are
literal identities. -/
example (Z : SSet.{u}) (a : SimplexCategoryᵒᵖ) :
    (SSet.diagonalConstIso Z).hom.app a = 𝟙 (Z.obj a) ∧
      (SSet.diagonalConstIso Z).inv.app a = 𝟙 (Z.obj a) :=
  ⟨rfl, rfl⟩

/-- The canonical isomorphism has the expected round trips. -/
example (Z : SSet.{u}) :
    (SSet.diagonalConstIso Z).hom ≫ (SSet.diagonalConstIso Z).inv = 𝟙 _ ∧
      (SSet.diagonalConstIso Z).inv ≫ (SSet.diagonalConstIso Z).hom = 𝟙 _ :=
  ⟨(SSet.diagonalConstIso Z).hom_inv_id,
    (SSet.diagonalConstIso Z).inv_hom_id⟩

/-- The relocated API remains available in arbitrary universes. -/
noncomputable example (Z : SSet.{0}) :
    SSet.simplicialDiagonalFunctor.obj
        ((SimplicialObject.const SSet.{0}).obj Z) ≅ Z :=
  SSet.diagonalConstIso Z

noncomputable example (Z : SSet.{1}) :
    SSet.simplicialDiagonalFunctor.obj
        ((SimplicialObject.const SSet.{1}).obj Z) ≅ Z :=
  SSet.diagonalConstIso Z

#print axioms SSet.diagonalConstIso

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SimplicialDiagonalTests

end
