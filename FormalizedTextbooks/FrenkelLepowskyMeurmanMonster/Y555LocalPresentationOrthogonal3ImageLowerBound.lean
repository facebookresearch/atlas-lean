/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual local reflection-image order from fully checked source root transports. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3ImageLowerBoundProofs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCMembershipSource

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine eight-generator source reflection image has at least 9170703360 elements. -/
theorem y322Orthogonal3Image_card_ge : 9170703360 ≤ Nat.card y322Orthogonal3Image :=
  y322Orthogonal3Image_card_ge_of_distinct y322Orthogonal3TCRepresentative_roots_injective

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
