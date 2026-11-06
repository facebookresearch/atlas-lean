/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer coefficient reads of the actual code-five positive-triality packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinDense

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual first odd-column quarter-weight sign, after retaining the initial V phase. -/
def monsterNortonCodeFiveForwardPhase : ℤ :=
  nortonUIntegerSign (golayMaskWeight (golayEncodedMask 948) / 4 : ℕ)

/-- The exact integer short read before division by sixty-four. -/
def monsterNortonCodeFiveForwardShortRead (p : Fin 32 × Fin 8) : ℤ :=
  let d := monsterNortonCodeFiveForwardOddCodes p.1
  let j := monsterNortonCodeFiveForwardColumns p.2
  monsterNortonCodeFiveForwardPhase *
    nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      (monsterNortonMixedOddSpinDense 1 ⟨d.val, by omega⟩ +
        monsterNortonMixedOddSpinDense 1 ⟨d.val + 2048, by omega⟩) *
      monsterNortonUNumerator1 3 j

/-- The exact integer physical tensor read before division by sixty-four square-root two. -/
def monsterNortonCodeFiveForwardTensorRead (p : Fin 64 × Fin 8) : ℤ :=
  let d : Fin 2048 := ⟨(monsterNortonCodeFiveForwardSpinLabel p.1).val % 2048,
    Nat.mod_lt _ (by decide)⟩
  let j := monsterNortonCodeFiveForwardColumns p.2
  monsterNortonCodeFiveForwardPhase *
    nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      (if (golayEncodedMask d.val).testBit j.val then -1 else 1) *
      (monsterNortonMixedOddSpinDense 1 ⟨d.val, by omega⟩ -
        monsterNortonMixedOddSpinDense 1 ⟨d.val + 2048, by omega⟩) *
      monsterNortonUNumerator1 3 j

set_option maxHeartbeats 16000000 in
-- Check all 256 genuine short reads from the complete proved source-spin table.
/-- The actual integer short reads give every proposed forward short coefficient. -/
theorem monsterNortonCodeFiveForwardShortRead_coefficient (p : Fin 32 × Fin 8) :
    monsterNortonCodeFiveForwardShortRead p =
      2 * monsterNortonCodeFiveForwardShortCoefficient p.1 p.2 := by
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check all 512 genuine tensor reads with the actual inverse-U physical column.
/-- The actual integer tensor reads give every proposed forward tensor coefficient. -/
theorem monsterNortonCodeFiveForwardTensorRead_coefficient (p : Fin 64 × Fin 8) :
    monsterNortonCodeFiveForwardTensorRead p =
      2 * monsterNortonCodeFiveForwardTensorCoefficient p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
