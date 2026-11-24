/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Preadditivity of the native category of indexed families

Existing hom groups are assembled pointwise. Object, morphism and indexing
universes remain independent, and the category is the native Pi category.
-/

@[expose] public section
noncomputable section

universe u v w

namespace CategoryTheory.Pi

variable {I : Type w} (D : I → Type u) [∀ i, Category.{v} (D i)] [∀ i, Preadditive (D i)]

/-- Pointwise hom groups make the native Pi category preadditive. -/
instance indexedPreadditive : Preadditive (∀ i, D i) where
  homGroup X Y := inferInstanceAs (AddCommGroup (∀ i : I, X i ⟶ Y i))
  add_comp X Y Z f f' g := by
    funext i
    exact Preadditive.add_comp (X i) (Y i) (Z i) (f i) (f' i) (g i)
  comp_add X Y Z f g g' := by
    funext i
    exact Preadditive.comp_add (X i) (Y i) (Z i) (f i) (g i) (g' i)

end CategoryTheory.Pi
