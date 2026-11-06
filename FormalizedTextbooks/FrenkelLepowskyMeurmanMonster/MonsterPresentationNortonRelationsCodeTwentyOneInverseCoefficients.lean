/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete integer coordinate reads of the actual code-twentyone inverse-sixth packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneInverseCoefficientCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete integer octad-short coefficient read before division by sixty-four. -/
def monsterNortonCodeTwentyOneInverseShortRead (p : Fin 8 × Fin 32) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonRemainingOctadUOutputIsOctad 8 e = true ∧
      monsterNortonRemainingOctadUOutputChoice 8 e =
        monsterNortonCodeTwentyOneInverseOctadChoice p.1 then
      monsterNortonCodeTwentyOneInverseCoefficientCache e *
        monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyOneInverseSign p.1 p.2)
          (monsterNortonRemainingOctadUOutputSign 8 e)
    else 0

/-- The complete integer tensor coordinate read before division by eight square-root two. -/
def monsterNortonCodeTwentyOneInverseTensorRead (p : Fin 16 × Fin 4) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonRemainingOctadUOutputIsOctad 8 e ≠ true ∧
      (monsterNortonRemainingOctadUOutputOddCode 8 e).val =
        (monsterNortonCodeTwentyOneInverseSpinLabel p.1).val % 2048 ∧
      monsterNortonRemainingOctadUOutputOddPosition 8 e =
        monsterNortonCodeTwentyOneInverseColumns p.2 then
      monsterNortonCodeTwentyOneInverseCoefficientCache e *
        (if (monsterNortonCodeTwentyOneInverseSpinLabel p.1).val < 2048 then 1 else -1) *
        (if (golayEncodedMask
          (monsterNortonRemainingOctadUOutputOddCode 8 e).val).testBit
            (monsterNortonCodeTwentyOneInverseColumns p.2).val then -1 else 1)
    else 0

set_option maxHeartbeats 16000000 in
-- All 256 short reads sum the complete sixty-four-term inverse packet with every phase.
/-- Every whole inverse short read gives its proposed normalized coefficient. -/
theorem monsterNortonCodeTwentyOneInverseShortRead_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeTwentyOneInverseShortRead p =
      2 * monsterNortonCodeTwentyOneInverseShortCoefficient p.1 p.2 := by
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- All 64 tensor reads retain every reached odd-source contribution of the inverse packet.
/-- Every whole inverse tensor read gives its proposed normalized coefficient. -/
theorem monsterNortonCodeTwentyOneInverseTensorRead_coefficient (p : Fin 16 × Fin 4) :
    4 * monsterNortonCodeTwentyOneInverseTensorRead p =
      monsterNortonCodeTwentyOneInverseTensorCoefficient p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
