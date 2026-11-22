/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# The original left-parameter prism dictionary

The existing internal-Hom prism dictionary uses `X ⊗ Δ[n]`. The native
Cartesian braiding identifies it with `Δ[n] ⊗ X`, the order used by marked
parameter products. Both directions retain the whole original prism and
all simplicial restriction and postcomposition maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SSet

/-- Read the simplex of the original function object from a left-parameter prism. -/
def leftIhomSimplexOfPrism {X Y : SSet.{u}} {n : ℕ} (f : (Δ[n] : SSet.{u}) ⊗ X ⟶ Y) :
    ((ihom X).obj Y) _⦋n⦌ :=
  ihomSimplexOfPrism ((β_ X (Δ[n] : SSet.{u})).hom ≫ f)

/-- Recover the same original left-parameter prism from a function-object simplex. -/
def leftIhomPrismOfSimplex {X Y : SSet.{u}} {n : ℕ} (s : ((ihom X).obj Y) _⦋n⦌) :
    (Δ[n] : SSet.{u}) ⊗ X ⟶ Y :=
  (β_ X (Δ[n] : SSet.{u})).inv ≫ ihomPrismOfSimplex s

@[simp]
theorem leftIhomPrismOfSimplex_simplex {X Y : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⊗ X ⟶ Y) :
    leftIhomPrismOfSimplex (leftIhomSimplexOfPrism f) = f := by
  simp [leftIhomPrismOfSimplex, leftIhomSimplexOfPrism]

@[simp]
theorem leftIhomSimplexOfPrism_prism {X Y : SSet.{u}} {n : ℕ}
    (s : ((ihom X).obj Y) _⦋n⦌) :
    leftIhomSimplexOfPrism (leftIhomPrismOfSimplex s) = s := by
  simp [leftIhomPrismOfSimplex, leftIhomSimplexOfPrism, ← Category.assoc]

/-- The original parameter-product maps and function-object simplices are equivalent in every degree. -/
def leftIhomSimplexEquiv (X Y : SSet.{u}) (n : ℕ) :
    ((Δ[n] : SSet.{u}) ⊗ X ⟶ Y) ≃ ((ihom X).obj Y) _⦋n⦌ where
  toFun := leftIhomSimplexOfPrism
  invFun := leftIhomPrismOfSimplex
  left_inv := leftIhomPrismOfSimplex_simplex
  right_inv := leftIhomSimplexOfPrism_prism

/-- Every original simplicial operator restricts the left parameter by its native tensor map. -/
theorem leftIhomSimplexOfPrism_map {X Y : SSet.{u}} {m n : SimplexCategory}
    (a : m ⟶ n) (f : (stdSimplex.obj n) ⊗ X ⟶ Y) :
    ((ihom X).obj Y).map a.op (leftIhomSimplexOfPrism f) =
      leftIhomSimplexOfPrism ((stdSimplex.map a ▷ X) ≫ f) := by
  dsimp only [leftIhomSimplexOfPrism, ihomSimplexOfPrism]
  rw [yonedaEquiv_naturality, ← curry_natural_left]
  congr 1

/-- The original target map postcomposes the whole left prism. -/
theorem leftIhomSimplexOfPrism_post {X Y Z : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⊗ X ⟶ Y) (g : Y ⟶ Z) :
    ((ihom X).map g).app (op ⦋n⦌) (leftIhomSimplexOfPrism f) =
      leftIhomSimplexOfPrism (f ≫ g) := by
  dsimp only [leftIhomSimplexOfPrism, ihomSimplexOfPrism]
  rw [← yonedaEquiv_comp, ← curry_natural_right, Category.assoc]

end SSet
