/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightShortCache
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightIncomingShortCertificates

/-! An exact zero of the complete original incoming root-eight short packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original incoming short coordinate at label0 and physical coordinate0 vanishes. -/
private theorem incoming_short_zero_cached :
    generatedFifthRootEightShortCachedCoefficient (Sum.inr (Sum.inr (0, 0))) = 0 := by
  decide +kernel

/-- The complete signed source cache proves the actual incoming coefficient is zero. -/
theorem generatedFifthRootEight_incoming_short_zero_at_origin :
    generatedAxisGlobalFifthRoot08Packet.2.1 (Sum.inr (Sum.inr (0, 0))) = 0 := by
  rw [generatedFifthRootEight_incoming_short_actual,
    ← generatedFifthRootEight_short_cached_coefficient_actual, incoming_short_zero_cached]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
