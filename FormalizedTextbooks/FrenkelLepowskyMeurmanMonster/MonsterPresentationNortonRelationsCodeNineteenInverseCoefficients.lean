/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete integer coordinate reads of the actual code-nineteen inverse-sixth packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenInverseCoefficientCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete integer octad-short coefficient read before division by sixty-four. -/
def monsterNortonCodeNineteenInverseShortRead (p : Fin 8 × Fin 32) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonRemainingOctadUOutputIsOctad 6 e = true ∧
      monsterNortonRemainingOctadUOutputChoice 6 e =
        monsterNortonCodeNineteenInverseOctadChoice p.1 then
      monsterNortonCodeNineteenInverseCoefficientCache e *
        monsterNortonOctadPositiveInteger (monsterNortonCodeNineteenInverseSign p.1 p.2)
          (monsterNortonRemainingOctadUOutputSign 6 e)
    else 0

/-- The complete integer tensor coordinate read before division by eight square-root two. -/
def monsterNortonCodeNineteenInverseTensorRead (p : Fin 16 × Fin 4) : ℤ :=
  ∑ e : Fin 64,
    if monsterNortonRemainingOctadUOutputIsOctad 6 e ≠ true ∧
      (monsterNortonRemainingOctadUOutputOddCode 6 e).val =
        (monsterNortonCodeNineteenInverseSpinLabel p.1).val % 2048 ∧
      monsterNortonRemainingOctadUOutputOddPosition 6 e =
        monsterNortonCodeNineteenInverseColumns p.2 then
      monsterNortonCodeNineteenInverseCoefficientCache e *
        (if (monsterNortonCodeNineteenInverseSpinLabel p.1).val < 2048 then 1 else -1) *
        (if (golayEncodedMask
          (monsterNortonRemainingOctadUOutputOddCode 6 e).val).testBit
            (monsterNortonCodeNineteenInverseColumns p.2).val then -1 else 1)
    else 0

set_option maxHeartbeats 16000000 in
-- All 256 short reads sum the complete sixty-four-term inverse packet with every phase.
/-- Every whole inverse short read gives its proposed normalized coefficient. -/
theorem monsterNortonCodeNineteenInverseShortRead_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeNineteenInverseShortRead p =
      2 * monsterNortonCodeNineteenInverseShortCoefficient p.1 p.2 := by
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- All 64 tensor reads retain every reached odd-source contribution of the inverse packet.
/-- Every whole inverse tensor read gives its proposed normalized coefficient. -/
theorem monsterNortonCodeNineteenInverseTensorRead_coefficient (p : Fin 16 × Fin 4) :
    4 * monsterNortonCodeNineteenInverseTensorRead p =
      monsterNortonCodeNineteenInverseTensorCoefficient p := by
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
