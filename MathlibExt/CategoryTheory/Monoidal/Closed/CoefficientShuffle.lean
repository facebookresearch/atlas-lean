/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braided coefficient shuffles

Defines the associator-braiding map from `M ⊗ (A ⊗ H)` to `A ⊗ (M ⊗ H)` in a braided monoidal
category. The shuffle is natural in the first coefficient.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory.CoefficientShuffle
variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [BraidedCategory V]

/-- The original coefficient-first shuffle retains the complete coefficient and parameter spaces. -/
def map (M A H : V) : M ⊗ (A ⊗ H) ⟶ A ⊗ (M ⊗ H) :=
  (α_ M A H).inv ≫ ((β_ M A).hom ▷ H) ≫ (α_ A M H).hom

/-- Every original coefficient map passes through the same full shuffle using the original
associator and braiding naturalities. -/
theorem naturality_first {M P : V} (f : M ⟶ P) (A H : V) :
    (f ▷ (A ⊗ H)) ≫ map P A H = map M A H ≫ (A ◁ (f ▷ H)) := by
  simp only [map, Category.assoc]
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left, comp_whiskerRight_assoc,
    associator_naturality_middle]

end CategoryTheory.MonoidalCategory.CoefficientShuffle
