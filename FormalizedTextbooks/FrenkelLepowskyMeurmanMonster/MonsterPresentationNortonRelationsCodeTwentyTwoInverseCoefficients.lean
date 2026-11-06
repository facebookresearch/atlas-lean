/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete integer coordinate reads of the actual code-twenty-two inverse-sixth packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoInverseCoefficientCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete integer octad-short coefficient read before division by sixty-four. -/
def monsterNortonCodeTwentyTwoInverseShortRead (p : Fin 16 × Fin 32) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonRemainingOctadUOutputIsOctad 9 e = true ∧
      monsterNortonRemainingOctadUOutputChoice 9 e =
        monsterNortonCodeTwentyTwoInverseOctadChoice p.1 then
      monsterNortonCodeTwentyTwoInverseCoefficientCache e *
        monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyTwoInverseSign p.1 p.2)
          (monsterNortonRemainingOctadUOutputSign 9 e)
    else 0

/-- The complete integer tensor coordinate read before division by eight square-root two. -/
def monsterNortonCodeTwentyTwoInverseTensorRead (p : Fin 16 × Fin 4) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonRemainingOctadUOutputIsOctad 9 e ≠ true ∧
      (monsterNortonRemainingOctadUOutputOddCode 9 e).val =
        (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2).val % 2048 ∧
      monsterNortonRemainingOctadUOutputOddPosition 9 e =
        monsterNortonCodeTwentyTwoInverseColumns p.1 then
      monsterNortonCodeTwentyTwoInverseCoefficientCache e *
        (if (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2).val < 2048 then 1 else -1) *
        (if (golayEncodedMask
          (monsterNortonRemainingOctadUOutputOddCode 9 e).val).testBit
            (monsterNortonCodeTwentyTwoInverseColumns p.1).val then -1 else 1)
    else 0

set_option maxHeartbeats 16000000 in
-- All 512 short reads sum the complete sixty-four-term inverse packet with every phase.
/-- Every whole inverse short read gives its proposed normalized coefficient. -/
theorem monsterNortonCodeTwentyTwoInverseShortRead_coefficient (p : Fin 16 × Fin 32) :
    monsterNortonCodeTwentyTwoInverseShortRead p =
      2 * monsterNortonCodeTwentyTwoInverseShortCoefficient p.1 p.2 := by
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- All 64 tensor reads retain every reached odd-source contribution of the inverse packet.
/-- Every whole inverse tensor read gives its proposed normalized coefficient. -/
theorem monsterNortonCodeTwentyTwoInverseTensorRead_coefficient (p : Fin 16 × Fin 4) :
    4 * monsterNortonCodeTwentyTwoInverseTensorRead p =
      monsterNortonCodeTwentyTwoInverseTensorCoefficient p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
