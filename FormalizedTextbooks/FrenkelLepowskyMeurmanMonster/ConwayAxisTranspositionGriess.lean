/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisTransposition

/-! The actual axis transposition formula in the original Griess representation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual signed-short local involution is recovered from its actual
Griess axis by Conway's denominator-cleared polynomial. -/
theorem conwayShortAxis_transposition_polynomial (r : GriessShortIndex) (c : ZMod 2)
    (x : GriessSpace) :
    (14 : ℝ) • (rhoLocal (inclQ (qCentral c * griessShortQ r)) x) =
      (14 : ℝ) • x - (24 : ℝ) • (griessForm (conwayShortAxis r c) x • conwayShortAxis r c) -
      (16 : ℝ) • griessProd (conwayShortAxis r c) x +
      griessProd (conwayShortAxis r c) (griessProd (conwayShortAxis r c) x) := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncodeLinear _ = griessConwayEncodeLinear _
  rw [map_smul, map_add, map_sub, map_sub, map_smul, map_smul, map_smul, map_smul]
  change (14 : ℝ) • griessConwayEncode (localGriessRepresentation
      (localFiberIncl (qCentral c * griessShortQ r)) x) =
    (14 : ℝ) • griessConwayEncode x -
      (24 : ℝ) • (griessForm (conwayShortAxis r c) x • griessConwayEncode (conwayShortAxis r c)) -
      (16 : ℝ) • griessConwayEncode (griessProd (conwayShortAxis r c) x) +
      griessConwayEncode (griessProd (conwayShortAxis r c) (griessProd (conwayShortAxis r c) x))
  rw [localGriessRepresentation_encode, griessProd_encode, griessProd_encode,
    griessProd_encode, griessForm_eq_conwayRawForm, conwayShortAxis_encode]
  exact conwayShortAxisRaw_transposition_polynomial r c (griessConwayEncode x)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
