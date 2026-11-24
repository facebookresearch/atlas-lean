/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Waldhausen.ProductExactFunctor

/-!
# Low-level original product projection clients

These clients require only the componentwise Waldhausen product and exact
functor interfaces, with four independent object and morphism worlds.
-/

open CategoryTheory Limits

universe uA vA uB vB

namespace MathlibExtTest.CategoryTheory.Waldhausen.ProductExactFunctorTests

variable (A : Type uA) [Category.{vA} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
variable (B : Type uB) [Category.{vB} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]

/-- The original componentwise product structure used by both projections. -/
local instance originalProductWaldhausen : WaldhausenCategoryWithoutGluing (A × B) :=
  prodWaldhausen (C := A) (D := B)

/-- The original first projection has its canonical exactness certificate. -/
theorem firstProjection : (CategoryTheory.Prod.fst A B).IsWaldhausenExact :=
  Functor.IsWaldhausenExact.prodFst A B

/-- The original second projection has its canonical exactness certificate. -/
theorem secondProjection : (CategoryTheory.Prod.snd A B).IsWaldhausenExact :=
  Functor.IsWaldhausenExact.prodSnd A B

/-- Both certificates preserve the actual original component cofibration maps. -/
theorem originalCofibrationComponents {X Y : A × B} (i : X ⟶ Y)
    (hi : IsCofibration i) :
    IsCofibration i.1 ∧ IsCofibration i.2 :=
  ⟨(firstProjection A B).map_cofibration i hi,
    (secondProjection A B).map_cofibration i hi⟩

/-- The two exact projections preserve the original component pushout squares. -/
theorem originalPushoutComponents {X Y X' P : A × B}
    (i : X ⟶ Y) (f : X ⟶ X') (inl : X' ⟶ P) (inr : Y ⟶ P)
    (hi : IsCofibration i) (hP : IsPushout f i inl inr) :
    IsPushout f.1 i.1 inl.1 inr.1 ∧ IsPushout f.2 i.2 inl.2 inr.2 :=
  ⟨(firstProjection A B).map_pushout i f inl inr hi hP,
    (secondProjection A B).map_pushout i f inl inr hi hP⟩

end MathlibExtTest.CategoryTheory.Waldhausen.ProductExactFunctorTests
