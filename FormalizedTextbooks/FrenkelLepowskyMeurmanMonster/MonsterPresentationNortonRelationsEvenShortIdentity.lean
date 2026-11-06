/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A concrete actual-group identity test using twenty-three original even short units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortBasisClosure
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsGlobalShortIdentity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTwentyThreeGlobalIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Twenty-three actual pair/octet unit returns and the delta-zero tensor return force identity. -/
theorem monsterNortonGenerated_evenShort_identity (g : G)
    (hs : ∀ k : Fin 23,
      g.val (monsterNortonPureShort (monsterNortonEvenShortBasis k)) =
        monsterNortonPureShort (monsterNortonEvenShortBasis k))
    (ht : g.val monsterNortonTwentyThreeTensorVector = monsterNortonTwentyThreeTensorVector) :
    g = 1 := by
  obtain ⟨h, rfl⟩ := monsterNortonGenerated_fix_short_mem_local g
    (monsterNortonEvenShortBasis 0) (hs 0)
  let K : Subgroup Q := (Subgroup.centralizer {localIntoGenerated h}).comap qIntoGenerated
  have hz : qCentralInvolution ∈ K :=
    Subgroup.mem_centralizer_singleton_iff.mpr (localIntoGenerated_commute_central h).symm
  have hb (k : Fin 23) : monsterNortonShortQ (monsterNortonEvenShortBasis k) ∈ K := by
    have hc := monsterNortonLocal_fix_short_commutes h (monsterNortonEvenShortBasis k) (hs k)
    change qIntoGenerated (monsterNortonShortQ (monsterNortonEvenShortBasis k)) ∈
      Subgroup.centralizer {localIntoGenerated h}
    rw [monsterNortonShortQ_eq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hc.symm
  apply monsterNortonGenerated_twentyThree_global_identity (localIntoGenerated h) _ ht
  intro i hi
  have hlt : i.val < 23 := by
    have hh : i.val ≠ 23 := by
      intro he
      exact hi (Fin.ext he)
    omega
  let j : Fin 23 := ⟨i.val, hlt⟩
  have he : Fin.castAdd 1 j = i := Fin.ext rfl
  have hm := monsterNortonEvenShortBasis_coordinates_mem K hz hb j
  rw [he] at hm
  exact (Subgroup.mem_centralizer_singleton_iff.mp hm).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
