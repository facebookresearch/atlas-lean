/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The actual finite coproduct and its successor split

The chosen coproduct on the original `Fin (n+1)` labels is isomorphic to
its first original summand plus the coproduct of the successor labels.
Both full original injection directions are retained.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.FiniteCoproductSuccessor

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  {n : ℕ} (X : Fin (n + 1) → C)

/-- The exact original successor-labelled family. -/
abbrev tail : Fin n → C := fun i => X i.succ

/-- The original finite coproduct splits into its first summand and unchanged successor summands. -/
def iso : (∐ X) ≅ X 0 ⨿ ∐ tail X where
  hom := Sigma.desc (fun i => Fin.cases coprod.inl
    (fun j => Sigma.ι (tail X) j ≫ coprod.inr) i)
  inv := coprod.desc (Sigma.ι X 0) (Sigma.desc (fun i => Sigma.ι X i.succ))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  inv_hom_id := by
    apply coprod.hom_ext
    · simp
    · apply Sigma.hom_ext
      intro i
      simp

/-- The first actual original injection is the same first coproduct leg. -/
@[reassoc]
theorem first_hom : Sigma.ι X 0 ≫ (iso X).hom = coprod.inl := by
  simp [iso]

/-- Every successor original injection is its unchanged tail injection followed by the
second leg. -/
@[reassoc]
theorem successor_hom (i : Fin n) :
    Sigma.ι X i.succ ≫ (iso X).hom = Sigma.ι (tail X) i ≫ coprod.inr := by
  simp [iso]

end CategoryTheory.Limits.FiniteCoproductSuccessor
