/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderFrameCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co2OrderShortStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalOrder

/-! Exact orders derived from the actual lattice enumeration and actual stabilizers. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual Leech lattice isometry group has the exact Conway group order. -/
theorem co0_card_exact : Nat.card leechIsomSubgroup = 8315553613086720000 := by
  rw [leechIsomSubgroup_card_normEight, leechNormEight_card]

/-- The actual quotient by the two central signs has the exact Co₁ order. -/
theorem co1_card_exact : Nat.card Co1 = 4157776806543360000 := by
  have h := leechIsomSubgroup_card
  rw [co0_card_exact] at h
  omega

/-- The actual short-label stabilizer has the exact Co₂ order. -/
theorem co2Short_card_exact (r : GriessShortIndex) :
    Nat.card (co2ShortStabilizer r) = 42305421312000 :=
  co2Short_card_of_co1_card r co1_card_exact

/-- The actual local extension has its exact order. -/
theorem local_h_card_exact : Nat.card H = 139511839126336328171520000 := by
  rw [h_card, co1_card_exact]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
