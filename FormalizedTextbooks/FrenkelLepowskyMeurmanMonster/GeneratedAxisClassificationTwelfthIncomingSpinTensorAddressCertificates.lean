/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorAddressPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorFourierAddresses

/-! Complete genuine compact boundary and Fourier source-label certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- All compact monomial boundary addresses and full signs are bound to actual source factors. -/
theorem generatedTwelfth_incoming_spin_tensor_addresses :
    ∀ i n, generatedTwelfthIncomingSpinTensorAddressCondition i n := by
  intro i n
  fin_cases i
  · exact generatedTwelfth_incoming_spin_tensor_address_packet_00 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
