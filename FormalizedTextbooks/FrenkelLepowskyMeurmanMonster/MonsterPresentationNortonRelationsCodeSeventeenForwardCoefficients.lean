/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete integer reads of the actual octad-seventeen forward packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenForwardCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The full original octad Fourier short read before division by sixty-four. -/
def monsterNortonCodeSeventeenForwardShortRead (p : Fin 8 × Fin 32) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonEvenShortInverseUKind 17 e = 1 ∧
      monsterNortonEvenShortInverseUOctadSlot 17 e =
        monsterNortonCodeSeventeenForwardOctadChoice p.1 then
      monsterNortonCodeSeventeenForwardCoefficientCache e *
        monsterNortonOctadPositiveInteger (monsterNortonCodeSeventeenForwardSign p.1 p.2)
          (monsterNortonEvenShortInverseUOctadSign 17 e)
    else 0

/-- The full physical tensor read of every odd contribution, before division by eight
square-root two. -/
def monsterNortonCodeSeventeenForwardTensorRead (p : Fin 16 × Fin 4) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonEvenShortInverseUKind 17 e = 2 ∧
      (monsterNortonEvenShortInverseUOddCode 17 e).val =
        (monsterNortonCodeSeventeenForwardSpinLabel p.1).val % 2048 ∧
      monsterNortonEvenShortInverseUOddPosition 17 e =
        monsterNortonCodeSeventeenForwardColumns p.2 then
      monsterNortonCodeSeventeenForwardCoefficientCache e *
        (if (monsterNortonCodeSeventeenForwardSpinLabel p.1).val < 2048 then 1 else -1) *
        (if (golayEncodedMask (monsterNortonEvenShortInverseUOddCode 17 e).val).testBit
          (monsterNortonCodeSeventeenForwardColumns p.2).val then -1 else 1)
    else 0

set_option maxHeartbeats 16000000 in
-- Each coordinate sums the complete sixty-four-term actual phase cache.
/-- All 256 full short reads equal the complete proposed candidate coefficients. -/
theorem monsterNortonCodeSeventeenForwardShortRead_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeSeventeenForwardShortRead p =
      2 * monsterNortonCodeSeventeenForwardShortCoefficient p.1 p.2 := by
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Each coordinate includes every reached actual odd-source contribution.
/-- All 64 full tensor reads equal the complete proposed candidate coefficients. -/
theorem monsterNortonCodeSeventeenForwardTensorRead_coefficient (p : Fin 16 × Fin 4) :
    4 * monsterNortonCodeSeventeenForwardTensorRead p =
      monsterNortonCodeSeventeenForwardTensorCoefficient p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
