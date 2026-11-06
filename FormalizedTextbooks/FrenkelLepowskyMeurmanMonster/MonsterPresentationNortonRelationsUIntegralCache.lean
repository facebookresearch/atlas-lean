/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Identify the complete actual Norton integral word with its verified finite matrix cache. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLocalIntegral
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderBinary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The source word equals the certified matrix in the actual integral Leech basis. -/
theorem monsterNortonUIntegralAction_cache : monsterNortonUIntegralAction =
    monsterNortonUIntegral := by
  apply Matrix.ext
  intro i j
  have he := (monsterNortonUIntegralAction_basis (Pi.single j 1)).symm.trans
    (monsterNortonUFiber_leech_basis (Pi.single j 1))
  have hc := leechBasisMatrix_injective (leechCoordinateEmbedding_injective he)
  have hi := congrFun hc i
  simpa only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
