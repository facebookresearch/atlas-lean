/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete integer coordinate reads of the actual code-twenty inverse-sixth packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyInverseCoefficientCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete integer octad-short coefficient read before division by sixty-four. -/
def monsterNortonCodeTwentyInverseShortRead (p : Fin 8 × Fin 32) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonRemainingOctadUOutputIsOctad 7 e = true ∧
      monsterNortonRemainingOctadUOutputChoice 7 e =
        monsterNortonCodeTwentyInverseOctadChoice p.1 then
      monsterNortonCodeTwentyInverseCoefficientCache e *
        monsterNortonOctadPositiveInteger (monsterNortonCodeTwentyInverseSign p.1 p.2)
          (monsterNortonRemainingOctadUOutputSign 7 e)
    else 0

/-- The complete integer tensor coordinate read before division by eight square-root two. -/
def monsterNortonCodeTwentyInverseTensorRead (p : Fin 16 × Fin 4) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonRemainingOctadUOutputIsOctad 7 e ≠ true ∧
      (monsterNortonRemainingOctadUOutputOddCode 7 e).val =
        (monsterNortonCodeTwentyInverseSpinLabel p.1).val % 2048 ∧
      monsterNortonRemainingOctadUOutputOddPosition 7 e =
        monsterNortonCodeTwentyInverseColumns p.2 then
      monsterNortonCodeTwentyInverseCoefficientCache e *
        (if (monsterNortonCodeTwentyInverseSpinLabel p.1).val < 2048 then 1 else -1) *
        (if (golayEncodedMask
          (monsterNortonRemainingOctadUOutputOddCode 7 e).val).testBit
            (monsterNortonCodeTwentyInverseColumns p.2).val then -1 else 1)
    else 0

set_option maxHeartbeats 16000000 in
-- All 256 short reads sum the complete sixty-four-term inverse packet with every phase.
/-- Every whole inverse short read gives its proposed normalized coefficient. -/
theorem monsterNortonCodeTwentyInverseShortRead_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeTwentyInverseShortRead p =
      2 * monsterNortonCodeTwentyInverseShortCoefficient p.1 p.2 := by
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- All 64 tensor reads retain every reached odd-source contribution of the inverse packet.
/-- Every whole inverse tensor read gives its proposed normalized coefficient. -/
theorem monsterNortonCodeTwentyInverseTensorRead_coefficient (p : Fin 16 × Fin 4) :
    4 * monsterNortonCodeTwentyInverseTensorRead p =
      monsterNortonCodeTwentyInverseTensorCoefficient p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
