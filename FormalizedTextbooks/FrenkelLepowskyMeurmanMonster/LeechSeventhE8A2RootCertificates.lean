/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2RootData

/-! Ordinary-kernel certificates of genuine root coordinates and full signed generator images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Check the 960 integral coordinates in the original eight-root matrix.
/-- Every representative is the displayed integer combination of the genuine root basis. -/
theorem leechSeventhE8Root_local_certificate : ∀ r : Fin 120,
    generatedOctadIntegerRootMatrix *ᵥ leechSeventhE8RootCoefficients r =
      leechSeventhE8RootLocal r := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check all 120 norms, each a sum of eight original integral squares.
/-- Every actual root representative has integral squared norm thirty-two. -/
theorem leechSeventhE8Root_norm_certificate : ∀ r : Fin 120,
    (∑ i, (leechSeventhE8RootLocal r i) ^ 2) = 32 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- The finite literal sign and permutation arrays have 2160 entries each.
/-- Each original root action retains an actual sign of one or minus one. -/
theorem leechSeventhE8Root_sign_certificate : ∀ g : Fin 18, ∀ r : Fin 120,
    leechSeventhE8RootImageSign g r = 1 ∨ leechSeventhE8RootImageSign g r = -1 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Bind 2160 signed root images, each using the eight original integral coordinates.
/-- Every signed index image is the actual already verified section-generator root matrix. -/
theorem leechSeventhE8Root_image_certificate : ∀ g : Fin 18, ∀ r : Fin 120,
    generatedFifthSectionGeneratorInteger g *ᵥ leechSeventhE8RootCoefficients r =
      leechSeventhE8RootImageSign g r •
        leechSeventhE8RootCoefficients (leechSeventhE8RootImage g r) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
