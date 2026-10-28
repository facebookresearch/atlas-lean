/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortGeometry

/-! The actual short-vector classes adjacent at angle sixty degrees to the standard root. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Actual projective short-vector addresses with pairing of absolute value sixteen to 4(e0+e1). -/
abbrev leechRootedA2NeighborAddress :=
  {r : GriessShortIndex // griessShortIntegral r 0 + griessShortIntegral r 1 = 4 ∨
    griessShortIntegral r 0 + griessShortIntegral r 1 = -4}

/-- Original octad words containing both root coordinates. -/
abbrev leechRootedA2OctadCode :=
  {d : Fin 4096 // golayMaskWeight (golayEncodedMask d.val) = 8 ∧
    (golayEncodedMask d.val).testBit 0 = true ∧ (golayEncodedMask d.val).testBit 1 = true}

/-- Actual canonical octad signs equal on the first two occupied coordinates. -/
abbrev leechRootedA2OctadSign :=
  {e : Fin 64 // (trialityEvenMask e).testBit 0 = (trialityEvenMask e).testBit 1}

/-- Original odd words with opposite signs at the two root coordinates. -/
abbrev leechRootedA2OddCode :=
  {d : Fin 2048 // (golayEncodedMask d.val).testBit 0 ≠ (golayEncodedMask d.val).testBit 1}

/-- Three finite genuine-coordinate families, before their catalogue-index identification. -/
abbrev leechRootedA2NormalizedAddress :=
  (Fin 2 × Fin 2 × Fin 22) ⊕
    ((leechRootedA2OctadCode × leechRootedA2OctadSign) ⊕ (leechRootedA2OddCode × Fin 2))

set_option maxHeartbeats 64000000 in
-- Check all original4096 Golay words against the actual weight and two-coordinate conditions.
/-- Exactly seventy-seven original octads contain the root pair. -/
theorem leechRootedA2OctadCode_card : Fintype.card leechRootedA2OctadCode = 77 := by
  decide +kernel

/-- Exactly thirty-two canonical octad signs agree at the root coordinates. -/
theorem leechRootedA2OctadSign_card : Fintype.card leechRootedA2OctadSign = 32 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check all2048 original odd-code sign prescriptions on both actual root coordinates.
/-- Exactly1024 original odd prescriptions have the required opposite signs. -/
theorem leechRootedA2OddCode_card : Fintype.card leechRootedA2OddCode = 1024 := by
  decide +kernel

/-- The three normalized source families account for88+2464+2048 addresses. -/
theorem leechRootedA2NormalizedAddress_card :
    Fintype.card leechRootedA2NormalizedAddress = 4600 := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    leechRootedA2OctadCode_card, leechRootedA2OctadSign_card, leechRootedA2OddCode_card]

/-- A faithful identification with the actual catalogue transfers the complete count. -/
theorem leechRootedA2NeighborAddress_card_of_equiv
    (e : leechRootedA2NeighborAddress ≃ leechRootedA2NormalizedAddress) :
    Fintype.card leechRootedA2NeighborAddress = 4600 := by
  rw [Fintype.card_congr e, leechRootedA2NormalizedAddress_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
