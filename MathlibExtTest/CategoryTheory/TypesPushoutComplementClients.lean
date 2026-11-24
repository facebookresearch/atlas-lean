/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Limits.Types.PushoutComplement

/-! The complete original outside-image source point remains isolated in
its same genuine original type pushout. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.Types

namespace CategoryTheory.Limits.TypesPushoutComplementClients

/-- Equality in the actual original type pushout reflects equality at every original outside-image source point. -/
theorem originalPushoutComplementInjective {S X Y P : Type u} {f : S ⟶ X} {g : S ⟶ Y}
    {i : X ⟶ P} {j : Y ⟶ P} (h : IsPushout f g i j) [Mono f] (x y : X)
    (hx : ¬ ∃ a, f a = x) (he : i x = i y) : x = y := outside_inl_injective h x y hx he

end CategoryTheory.Limits.TypesPushoutComplementClients
