/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual coordinate tables for the five sparse mixed inverse spin numerators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinDenseSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The entire dense candidate table has its exact real spin norm 128. -/
theorem monsterNortonMixedOddSpinDense_norm (k : Fin 5) :
    spinPairing (nortonUIntegerEmbed (monsterNortonMixedOddSpinDense k))
      (nortonUIntegerEmbed (monsterNortonMixedOddSpinDense k)) = 128 := by
  rw [monsterNortonUIntegerEmbed_spin_norm, monsterNortonMixedOddSpinDense_norm_integer]
  norm_num

/-- All supported dense coordinates have maximal pairing with the full sparse packet. -/
theorem monsterNortonMixedOddSpinDense_pairing (k : Fin 5) :
    spinPairing (nortonUIntegerEmbed (monsterNortonMixedOddSpinDense k))
      (monsterNortonMixedOddSpinPacket k) = 128 := by
  rw [monsterNortonMixedOddSpinPacket, monsterNortonSpin_sparse_pairing]
  simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
    monsterNortonMixedOddSpinDense_support, ← pow_two]
  have hs (i : Fin 128) : (monsterNortonMixedOddSpinCoefficient k i : ℝ) ^ 2 = 1 := by
    exact_mod_cast monsterNortonMixedOddSpinCoefficient_sq k i
  simp_rw [hs]
  norm_num

/-- The complete coordinate table equals the full sparse vector, including all outside zeros. -/
theorem monsterNortonMixedOddSpinDense_sparse (k : Fin 5) :
    nortonUIntegerEmbed (monsterNortonMixedOddSpinDense k) = monsterNortonMixedOddSpinPacket k := by
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonMixedOddSpinDense_norm, monsterNortonMixedOddSpinPacket_norm]
  · rw [monsterNortonMixedOddSpinDense_pairing, monsterNortonMixedOddSpinDense_norm]

/-- The full actual inverse spin numerator is exactly the finite coordinate table at every index. -/
theorem monsterNortonMixedOddSpinNumerator_dense (k : Fin 5) :
    nortonUIntegerEmbed (monsterNortonMixedOddSpinNumerator k) =
      nortonUIntegerEmbed (monsterNortonMixedOddSpinDense k) := by
  rw [monsterNortonMixedOddSpinNumerator_sparse, monsterNortonMixedOddSpinDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
