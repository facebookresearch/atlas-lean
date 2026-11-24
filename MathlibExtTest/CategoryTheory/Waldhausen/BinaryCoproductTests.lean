/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproduct

/-!
# Tests for Waldhausen binary coproduct data

These clients pin the chosen cocone, its named non-instance
`HasBinaryCoproducts` value, the coproduct equations, and the pushout-of-zero
orientation.  No global coproduct instance is installed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen
namespace BinaryCoproductTests

variable {C : Type u} [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

example (F : Discrete WalkingPair ⥤ C) :
    Nonempty (ColimitCocone F) :=
  CategoryTheory.Waldhausen.binaryCoproductColimitCocone_nonempty C F

example (F : Discrete WalkingPair ⥤ C) : ColimitCocone F :=
  CategoryTheory.Waldhausen.binaryCoproductColimitCocone C F

example : HasBinaryCoproducts C :=
  CategoryTheory.Waldhausen.waldhausenHasBinaryCoproducts C

#guard_msgs (error, substring := true) in
#synth HasBinaryCoproducts C

example {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    letI : HasBinaryCoproducts C :=
      CategoryTheory.Waldhausen.waldhausenHasBinaryCoproducts C
    coprod.inl ≫ coprod.desc f g = f ∧
      coprod.inr ≫ coprod.desc f g = g := by
  let _ : HasBinaryCoproducts C :=
    CategoryTheory.Waldhausen.waldhausenHasBinaryCoproducts C
  simp

example (X Y : C) :
    let F : Discrete WalkingPair ⥤ C := pair X Y
    let c := CategoryTheory.Waldhausen.binaryCoproductColimitCocone C F
    IsPushout ((isZero_zero C).isInitial.to X)
      ((isZero_zero C).isInitial.to Y)
      (c.cocone.ι.app ⟨WalkingPair.left⟩)
      (c.cocone.ι.app ⟨WalkingPair.right⟩) := by
  let F : Discrete WalkingPair ⥤ C := pair X Y
  let c := CategoryTheory.Waldhausen.binaryCoproductColimitCocone C F
  dsimp only [F] at c
  exact IsPushout.of_is_coproduct c.isColimit (isZero_zero C).isInitial

section TypeZero

variable {C₀ : Type} [Category.{0} C₀] [HasZeroObject C₀]
  [WaldhausenCategoryWithoutGluing C₀]

example : HasBinaryCoproducts C₀ :=
  CategoryTheory.Waldhausen.waldhausenHasBinaryCoproducts C₀

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [HasZeroObject C₁]
  [WaldhausenCategoryWithoutGluing C₁]

example : HasBinaryCoproducts C₁ :=
  CategoryTheory.Waldhausen.waldhausenHasBinaryCoproducts C₁

end TypeOne

#print axioms CategoryTheory.Waldhausen.binaryCoproductColimitCocone_nonempty
#print axioms CategoryTheory.Waldhausen.binaryCoproductColimitCocone
#print axioms CategoryTheory.Waldhausen.waldhausenHasBinaryCoproducts

end BinaryCoproductTests
end MathlibExtTest.CategoryTheory.Waldhausen
