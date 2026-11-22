/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Closed.CoefficientShuffle

/-!
# Naturality of coefficient shuffles

In a braided monoidal category, the coefficient shuffle M ⊗ (A ⊗ H) ⟶ A ⊗ (M ⊗ H) is natural
in A and H. Both equations keep the indicated whiskering maps and tensor reassociations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace NativeOmegaPreparation.CoefficientShuffle
variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [BraidedCategory V]

/-- Every original coefficient-space arrow passes through the complete coefficient shuffle. -/
theorem naturality_second (M : V) {A B : V} (f : A ⟶ B) (H : V) :
    (M ◁ (f ▷ H)) ≫ map M B H = map M A H ≫ (f ▷ (M ⊗ H)) := by
  simp only [map, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
    associator_naturality_left]

/-- Every entire input-object arrow passes through the same coefficient shuffle, before or after
currying. -/
theorem naturality_third (M A : V) {H K : V} (f : H ⟶ K) :
    (M ◁ (A ◁ f)) ≫ map M A K = map M A H ≫ (A ◁ (M ◁ f)) := by
  simp only [map, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right]

end NativeOmegaPreparation.CoefficientShuffle
