/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthThreeCandidateIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorAddressPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorAddressPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorAddressPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorFourierAddresses

/-! All complete source addresses for the three genuine candidates required by projection generation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Complete preferred source addresses and signs of each needed candidate. -/
theorem generatedTwelfth_three_spin_tensor_addresses :
    ∀ (g : Fin 3) n, generatedTwelfthSpinTensorAddressCondition (generatedTwelfthThreeCandidateIndex g) n := by
  intro g n
  fin_cases g
  · exact generatedTwelfth_spin_tensor_address_packet_00 n
  · exact generatedTwelfth_spin_tensor_address_packet_01 n
  · exact generatedTwelfth_spin_tensor_address_packet_02 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
