/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Presentable.Limits

/-!
# Same-rank compactness of actual original pushouts

The actual original span and its chosen pushout UP prove compactness
from the three genuine original compact objects, without a new-UP premise.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.CompactPushoutPresentability

open Limits

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {D X Y : C} (u : D ⟶ X) (f : D ⟶ Y) [HasPushout u f]
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  [IsCardinalPresentable D chi] [IsCardinalPresentable X chi] [IsCardinalPresentable Y chi]

/-- The original chosen pushout is compact at the same original regular rank. -/
theorem presentable : IsCardinalPresentable (pushout u f) chi := by
  let (j : WalkingSpan) : IsCardinalPresentable ((span u f).obj j) chi := match j with
    | WalkingSpan.zero => inferInstanceAs (IsCardinalPresentable D chi)
    | WalkingSpan.left => inferInstanceAs (IsCardinalPresentable X chi)
    | WalkingSpan.right => inferInstanceAs (IsCardinalPresentable Y chi)
  exact isCardinalPresentable_of_isColimit (pushout.cocone u f) (pushout.isColimit u f) chi
    (hasCardinalLT_of_finite (Arrow WalkingSpan) chi (Fact.out : chi.IsRegular).aleph0_le)

end CategoryTheory.SmallObject.CompactPushoutPresentability
