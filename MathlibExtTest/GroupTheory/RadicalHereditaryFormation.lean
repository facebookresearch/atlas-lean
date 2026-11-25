/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.RadicalHereditaryFormation

open MathlibExt.GroupTheory.RadicalHereditaryFormationKourovka12Problem7Wanted

namespace MathlibExtTest.GroupTheory.RadicalHereditaryFormation

private def solubleGroups : GroupClass where
  mem H _ := Group.IsSolvable H
  iso G _ _ _ e hg := by
    have : Group.IsSolvable G := hg
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

-- For a soluble group the maximality clause forces the radical to be the whole group.
example {G : Type} [Group G] [Group.IsSolvable G] {R : Subgroup G}
    (h : IsSolubleRadical R) : R = ⊤ :=
  top_le_iff.mp (h.2.2 ⊤ inferInstance inferInstance)

-- The class of soluble groups lifts membership through the radical's Frattini subgroup.
example : IsComposition solubleGroups := by
  rintro G _ _ R hR ⟨hn, hq⟩
  have := hR.2.1
  let F := (frattini R).map R.subtype
  have : Group.IsSolvable F := Group.isSolvable_of_surjective
    (R.subtype.subgroupMap_surjective (frattini R))
  have : Group.IsSolvable (G ⧸ F) := hq
  exact Group.isSolvable_of_subgroup_quotient F

-- The refutation supplies a single class satisfying all three closure conditions.
example : ∃ X : GroupClass, IsFormation X ∧ IsRadical X ∧ IsHereditary X ∧ ¬ IsComposition X := by
  by_contra h
  apply radicalHereditaryFormationIsComposition_refuted
  intro X hF hR hH
  by_contra hc
  exact h ⟨X, hF, hR, hH, hc⟩

end MathlibExtTest.GroupTheory.RadicalHereditaryFormation
