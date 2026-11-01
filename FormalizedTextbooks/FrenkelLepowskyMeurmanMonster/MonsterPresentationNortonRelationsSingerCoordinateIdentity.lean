/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A single actual tensor coefficient finishes the genuine twenty-three-coordinate identity test. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTwentyThreeGlobalIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Twenty-three full Q checks and one actual delta-zero tensor coefficient force identity in G. -/
theorem monsterNortonGenerated_twentyThree_coefficient_identity (g : G)
    (hi : ∀ i : Fin 24, i ≠ 23 → Commute g (qIntoGenerated (qCoordinateGenerator i)))
    (hx : (griessConwayEncode (g.val monsterNortonTwentyThreeTensorVector)).2.2 0 0 = 1) :
    g = 1 := by
  obtain ⟨h, hh⟩ := monsterNortonGenerated_twentyThree_mem_local g hi
  have hiH : ∀ i : Fin 24, i ≠ 23 → Commute h (inclQ (qCoordinateGenerator i)) := by
    intro i hi23
    change h * inclQ (qCoordinateGenerator i) = inclQ (qCoordinateGenerator i) * h
    apply localIntoGenerated_injective
    rw [map_mul, map_mul]
    change localIntoGenerated h * qIntoGenerated (qCoordinateGenerator i) =
      qIntoGenerated (qCoordinateGenerator i) * localIntoGenerated h
    rw [hh]
    exact (hi i hi23).eq
  obtain ⟨q, hq⟩ := monsterNortonLocal_twentyThree_mem_Q h hiH
  have hqg : qIntoGenerated q = g := by
    change localIntoGenerated (inclQ q) = g
    rw [hq, hh]
  have hiQ : ∀ i : Fin 24, i ≠ 23 → Commute q (qCoordinateGenerator i) := by
    intro i hi23
    change q * qCoordinateGenerator i = qCoordinateGenerator i * q
    apply qIntoGenerated_injective
    rw [map_mul, map_mul, hqg]
    exact (hi i hi23).eq
  have hfix : spinRepresentation q (Pi.single 0 1) 0 = 1 := by
    rw [← hqg] at hx
    change (griessConwayEncode (localGriessRepresentation (localFiberIncl q)
      monsterNortonTwentyThreeTensorVector)).2.2 0 0 = 1 at hx
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_tensor,
      monsterNortonTwentyThreeTensorVector_encode] at hx
    change localTensorRepresentation (localFiberIncl q)
      (tensorColumnInsert 0 (Pi.single 0 1 : SpinSpace)) 0 0 = 1 at hx
    rw [localTensorRepresentation_q] at hx
    exact hx
  have hqone := monsterNortonQ_twentyThree_eq_one_of_spin_zero q hiQ hfix
  rw [hqone, map_one] at hqg
  exact hqg.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
