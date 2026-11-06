/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthQImage

/-! Intrinsic short-class injectivity recognizes actual coordinate images from preferred-Q bases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Equality of genuine preferred short bases identifies the actual preferred catalogue indices. -/
theorem generatedNinth_short_Q_base_injective :
    Function.Injective (fun r : GriessShortIndex => (griessShortQ r).base) := by
  intro r s h
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact congrArg Multiplicative.toAdd h

/-- A checked actual Q-base image identifies the literal spatial word's short-coordinate image. -/
theorem generatedNinth_short_image_of_base (r s : GriessShortIndex)
    (h : (generatedNinthQImage (griessShortQ r)).base = (griessShortQ s).base) :
    griessShortPermutation generatedNinthLocalFiber.val.2 r = s := by
  apply generatedNinth_short_Q_base_injective
  have he := griessShortQ_image_base generatedNinthLocalFiber r
  rw [generatedNinthQImage_eq] at he
  exact he.symm.trans h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
