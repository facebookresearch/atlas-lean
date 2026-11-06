/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeProjectionGeneration

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorAddressPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorAddressPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorAddressPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorFourierAddresses

/-! Complete genuine compact boundary and Fourier source-label certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- All compact monomial boundary addresses and full signs are bound to actual source factors. -/
theorem generatedNinth_lower_spin_three_tensor_addresses :
    ∀ g : Fin 3, ∀ n, generatedNinthLowerSpinTensorAddressCondition
      (generatedNinthLowerSpinThreeCandidateIndex g) n := by
  intro g n
  fin_cases g
  · exact generatedNinth_lower_spin_tensor_address_packet_00 n
  · exact generatedNinth_lower_spin_tensor_address_packet_09 n
  · exact generatedNinth_lower_spin_tensor_address_packet_10 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
