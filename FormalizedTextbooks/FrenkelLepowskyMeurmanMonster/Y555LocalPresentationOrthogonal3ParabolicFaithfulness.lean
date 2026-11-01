/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual source parabolic orders and faithful characteristic-three restrictions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3ParabolicLowerBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationImageCardinality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual A5 source subgroup and image both have order 720, and the restriction is faithful. -/
theorem y322Orthogonal3A5_exact_order_faithful :
    Nat.card y322A5Parabolic = 720 ∧ Nat.card y322Orthogonal3A5Image = 720 ∧
      Function.Injective (y322Orthogonal3Hom.comp y322A5Parabolic.subtype) := by
  let := y322A5Parabolic_finite
  exact y322FiniteSubgroup_image_exact_order y322Orthogonal3Hom y322A5Parabolic 720
    y322Orthogonal3A5Image_card_ge y322A5Parabolic_card_le

/-- The actual D6 source subgroup and image both have order 23040, with faithful restriction. -/
theorem y322Orthogonal3D6_exact_order_faithful :
    Nat.card y322D6Parabolic = 23040 ∧ Nat.card y322Orthogonal3D6Image = 23040 ∧
      Function.Injective (y322Orthogonal3Hom.comp y322D6Parabolic.subtype) := by
  let := y322D6Parabolic_finite
  exact y322FiniteSubgroup_image_exact_order y322Orthogonal3Hom y322D6Parabolic 23040
    y322Orthogonal3D6Image_card_ge y322D6Parabolic_card_le

/-- The actual E7 source subgroup and image have order 2903040, with faithful restriction. -/
theorem y322Orthogonal3E7_exact_order_faithful :
    Nat.card y322E7Parabolic = 2903040 ∧ Nat.card y322Orthogonal3E7Image = 2903040 ∧
      Function.Injective (y322Orthogonal3Hom.comp y322E7Parabolic.subtype) := by
  let := y322E7Parabolic_finite
  exact y322FiniteSubgroup_image_exact_order y322Orthogonal3Hom y322E7Parabolic 2903040
    y322Orthogonal3E7Image_card_ge y322E7Parabolic_card_le

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
