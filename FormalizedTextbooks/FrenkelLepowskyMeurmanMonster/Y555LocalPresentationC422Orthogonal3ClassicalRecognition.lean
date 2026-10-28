/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine original local source recognition as the independent split-form norm-two reflection
group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3Faithfulness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3IndependentImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3PlusForm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual original C422/S/Q source is isomorphic to the independent split-form reflection
group. -/
noncomputable def y422ClassicalReflectionEquiv :
    Y422Presentation ≃* y422Orthogonal3NormTwoProjectiveGroup :=
  y422Orthogonal3SourceImageEquiv.trans
    (MulEquiv.subgroupCongr y422Orthogonal3ProjectiveImage_eq_normTwoProjectiveGroup)

/-- Recognition preserves the exact actual projective value of every original source element. -/
theorem y422ClassicalReflectionEquiv_value (x : Y422Presentation) :
    (y422ClassicalReflectionEquiv x).val = y422Orthogonal3ProjectiveHom x := rfl

/-- Every original source generator retains its literal norm-two projective reflection. -/
theorem y422ClassicalReflectionEquiv_generator (i : Fin 9) :
    (y422ClassicalReflectionEquiv (PresentedGroup.of i)).val =
      Matrix.ProjGenLinGroup.mk (y422Orthogonal3Generator i) :=
  y422Orthogonal3ProjectiveHom_generator i

/-- The independently specified split-form norm-two projective reflection group has exact order. -/
theorem y422ClassicalReflectionGroup_card :
    Nat.card y422Orthogonal3NormTwoProjectiveGroup = 9904359628800 := by
  rw [← Nat.card_congr y422ClassicalReflectionEquiv.toEquiv]
  exact y422Orthogonal3_exact_order_faithful.1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
