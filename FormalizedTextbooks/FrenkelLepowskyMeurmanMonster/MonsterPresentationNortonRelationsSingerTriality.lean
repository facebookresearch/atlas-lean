/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual source Singer permutation commutes with genuine dictionary triality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerCoordinateChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerTrialityCoefficient

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All twenty-three actual source checks and the genuine tensor coefficient kill the commutator. -/
theorem monsterNortonSinger_triality_commutator_eq_one :
    localIntoGenerated monsterNortonSingerLocal⁻¹ * extraIntoGenerated⁻¹ *
      localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated = 1 :=
  monsterNortonGenerated_twentyThree_coefficient_identity _
    monsterNortonSinger_commutator_coordinates monsterNortonSinger_triality_coefficient

/-- The forward actual Singer lift commutes with the original extra action. -/
theorem monsterNortonSingerLocal_generated_commute_extra :
    Commute (localIntoGenerated monsterNortonSingerLocal) extraIntoGenerated := by
  have h : (extraIntoGenerated * localIntoGenerated monsterNortonSingerLocal)⁻¹ *
      (localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated) = 1 := by
    simpa only [map_inv, mul_inv_rev, mul_assoc] using
      monsterNortonSinger_triality_commutator_eq_one
  exact (inv_mul_eq_one.mp h).symm

/-- The actual inverse-transpose source Singer permutation commutes with source triality. -/
theorem monsterNortonSingerGenerated_commute_sourceTriality :
    Commute monsterNortonSingerGenerated monsterSourceTriality := by
  simpa only [monsterNortonSingerGenerated, monsterSourceTriality, map_inv] using
    monsterNortonSingerLocal_generated_commute_extra.inv_left.inv_right

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
