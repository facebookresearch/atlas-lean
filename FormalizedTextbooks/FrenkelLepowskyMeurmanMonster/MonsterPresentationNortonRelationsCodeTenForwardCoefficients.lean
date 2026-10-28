/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer coefficient reads of the actual code-ten positive-triality packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinDense

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual first odd-column quarter-weight sign, after retaining the initial V phase. -/
def monsterNortonCodeTenForwardPhase : ℤ :=
  nortonUIntegerSign (golayMaskWeight (golayEncodedMask 338) / 4 : ℕ)

/-- The exact integer short read before division by sixty-four. -/
def monsterNortonCodeTenForwardShortRead (p : Fin 32 × Fin 8) : ℤ :=
  let d := monsterNortonCodeTenForwardOddCodes p.1
  let j := monsterNortonCodeTenForwardColumns p.2
  monsterNortonCodeTenForwardPhase *
    nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      (monsterNortonMixedOddSpinDense 0 ⟨d.val, by omega⟩ +
        monsterNortonMixedOddSpinDense 0 ⟨d.val + 2048, by omega⟩) *
      monsterNortonUNumerator1 3 j

/-- The exact integer physical tensor read before division by sixty-four square-root two. -/
def monsterNortonCodeTenForwardTensorRead (p : Fin 64 × Fin 8) : ℤ :=
  let d : Fin 2048 := ⟨(monsterNortonCodeTenForwardSpinLabel p.1).val % 2048,
    Nat.mod_lt _ (by decide)⟩
  let j := monsterNortonCodeTenForwardColumns p.2
  monsterNortonCodeTenForwardPhase *
    nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      (if (golayEncodedMask d.val).testBit j.val then -1 else 1) *
      (monsterNortonMixedOddSpinDense 0 ⟨d.val, by omega⟩ -
        monsterNortonMixedOddSpinDense 0 ⟨d.val + 2048, by omega⟩) *
      monsterNortonUNumerator1 3 j

set_option maxHeartbeats 16000000 in
-- Check all 256 genuine short reads from the complete proved source-spin table.
/-- The actual integer short reads give every proposed forward short coefficient. -/
theorem monsterNortonCodeTenForwardShortRead_coefficient (p : Fin 32 × Fin 8) :
    monsterNortonCodeTenForwardShortRead p =
      2 * monsterNortonCodeTenForwardShortCoefficient p.1 p.2 := by
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check all 512 genuine tensor reads with the actual inverse-U physical column.
/-- The actual integer tensor reads give every proposed forward tensor coefficient. -/
theorem monsterNortonCodeTenForwardTensorRead_coefficient (p : Fin 64 × Fin 8) :
    monsterNortonCodeTenForwardTensorRead p =
      2 * monsterNortonCodeTenForwardTensorCoefficient p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
