/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The independent full Cartan isometry group has its proved finite upper bound. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3FullOrderProofs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3FullGroup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The full Cartan group is exactly the independent generic Gram-isometry group. -/
theorem y322Orthogonal3FullGroup_eq_gram :
    y322Orthogonal3FullGroup = y322GramIsometryGroup y322Orthogonal3Gram := by
  ext g
  rfl

/-- The independent full Cartan isometry group has order at most 18341406720. -/
theorem y322Orthogonal3FullGroup_card_le :
    Nat.card y322Orthogonal3FullGroup ≤ 18341406720 := by
  rw [y322Orthogonal3FullGroup_eq_gram]
  exact y322Orthogonal3GramGroup_card_le

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
