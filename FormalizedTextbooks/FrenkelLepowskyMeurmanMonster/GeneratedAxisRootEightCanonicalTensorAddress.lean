/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorAddressCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorFiniteCoordinates

/-! Assemble every original incoming tensor coordinate from complete bounded certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original monomial boundary label and complete sign is certified. -/
theorem generatedRootEight_canonical_tensor_addresses :
    ∀ n, generatedRootEightCanonicalTensorAddressCondition n := by
  apply generatedRootEight_incoming_tensor_coordinate_cover
  intro b u
  exact generatedRootEight_canonical_tensor_addresses_blocks b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
