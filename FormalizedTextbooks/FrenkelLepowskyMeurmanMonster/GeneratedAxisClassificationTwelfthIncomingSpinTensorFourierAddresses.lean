/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorCircuitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinLabelXor

/-! Every Fourier source label follows from genuine twelve-bit XOR semantics. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All individual Fourier source label changes are exact binary flips. -/
theorem generatedTwelfth_incoming_spin_tensor_fourier_addresses :
    ∀ k n, generatedTwelfthIncomingSpinTensorFourierAddressCondition k n := by
  intro k n
  exact generatedTwelfth_spin_label_xor k n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
