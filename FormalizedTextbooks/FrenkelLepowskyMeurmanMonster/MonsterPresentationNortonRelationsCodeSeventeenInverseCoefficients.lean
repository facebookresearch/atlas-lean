/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete integer coordinate reads of the actual code-seventeen inverse-sixth packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenInverseCoefficientCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete integer octad-short coefficient read before division by sixty-four. -/
def monsterNortonCodeSeventeenInverseShortRead (p : Fin 8 × Fin 32) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonRemainingOctadUOutputIsOctad 4 e = true ∧
      monsterNortonRemainingOctadUOutputChoice 4 e =
        monsterNortonCodeSeventeenInverseOctadChoice p.1 then
      monsterNortonCodeSeventeenInverseCoefficientCache e *
        monsterNortonOctadPositiveInteger (monsterNortonCodeSeventeenInverseSign p.1 p.2)
          (monsterNortonRemainingOctadUOutputSign 4 e)
    else 0

/-- The complete integer tensor coordinate read before division by eight square-root two. -/
def monsterNortonCodeSeventeenInverseTensorRead (p : Fin 16 × Fin 4) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonRemainingOctadUOutputIsOctad 4 e ≠ true ∧
      (monsterNortonRemainingOctadUOutputOddCode 4 e).val =
        (monsterNortonCodeSeventeenInverseSpinLabel p.1).val % 2048 ∧
      monsterNortonRemainingOctadUOutputOddPosition 4 e =
        monsterNortonCodeSeventeenInverseColumns p.2 then
      monsterNortonCodeSeventeenInverseCoefficientCache e *
        (if (monsterNortonCodeSeventeenInverseSpinLabel p.1).val < 2048 then 1 else -1) *
        (if (golayEncodedMask
          (monsterNortonRemainingOctadUOutputOddCode 4 e).val).testBit
            (monsterNortonCodeSeventeenInverseColumns p.2).val then -1 else 1)
    else 0

set_option maxHeartbeats 16000000 in
-- All 256 short reads sum the complete sixty-four-term inverse packet with every phase.
/-- Every whole inverse short read gives its proposed normalized coefficient. -/
theorem monsterNortonCodeSeventeenInverseShortRead_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeSeventeenInverseShortRead p =
      2 * monsterNortonCodeSeventeenInverseShortCoefficient p.1 p.2 := by
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- All 64 tensor reads retain every reached odd-source contribution of the inverse packet.
/-- Every whole inverse tensor read gives its proposed normalized coefficient. -/
theorem monsterNortonCodeSeventeenInverseTensorRead_coefficient (p : Fin 16 × Fin 4) :
    4 * monsterNortonCodeSeventeenInverseTensorRead p =
      monsterNortonCodeSeventeenInverseTensorCoefficient p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
