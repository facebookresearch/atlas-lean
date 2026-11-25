/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor

/-!
# Tests for Waldhausen-exact functors

These tests exercise identity, composition, and cofiber-sequence transport
through the public API.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace MathlibExtTest.CategoryTheory.Waldhausen.ExactFunctorTests

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]

example : (Functor.id C).IsWaldhausenExact :=
  Functor.IsWaldhausenExact.id

example (F : C ⥤ D) (G : D ⥤ E)
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) :
    (F ⋙ G).IsWaldhausenExact :=
  hF.comp hG

example (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {X Y Z : C} {i : X ⟶ Y} {p : Y ⟶ Z}
    (hSeq : IsCofibrationSequence (C := C) i p) :
    IsCofibrationSequence (C := D) (F.map i) (F.map p) :=
  hF.map_cofibrationSequence hSeq

end MathlibExtTest.CategoryTheory.Waldhausen.ExactFunctorTests
