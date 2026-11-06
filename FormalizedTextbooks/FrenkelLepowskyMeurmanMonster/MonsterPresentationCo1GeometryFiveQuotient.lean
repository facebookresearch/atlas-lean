/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The five concrete lattice operators generate the actual Conway quotient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryFiveGeneration

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The five actual Conway classes used by the finite source-module stability certificates. -/
def monsterCo1FiveGenerator (k : Fin 5) : Co1 := QuotientGroup.mk (omegaOrbitIsometry k)

/-- Their generated subgroup is defined inside the actual Conway quotient. -/
def monsterCo1FiveSubgroup : Subgroup Co1 :=
  Subgroup.closure (Set.range monsterCo1FiveGenerator)

/-- The quotient image of the five-isometry subgroup is the genuine class subgroup. -/
theorem monsterCo1FiveSubgroup_image :
    monsterCo1FiveIsometrySubgroup.map (QuotientGroup.mk' signsSubgroup) =
      monsterCo1FiveSubgroup := by
  rw [monsterCo1FiveIsometrySubgroup, MonoidHom.map_closure, ← Set.range_comp]
  rfl

/-- The same five concrete Conway operators generate the full actual Conway group. -/
theorem monsterCo1FiveSubgroup_eq_top : monsterCo1FiveSubgroup = ⊤ := by
  rw [← monsterCo1FiveSubgroup_image, monsterCo1FiveIsometrySubgroup_eq_top, Subgroup.map_top]
  exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective signsSubgroup)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
