/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.MinimalIntersectionsFittingKourovka20Problem122

open MathlibExt.GroupTheory.MinimalIntersectionsFittingKourovka20Problem122Wanted

variable {G : Type} [Group G] (A B C : Subgroup G)

-- If one intersection is trivial, it is the unique inclusion-minimal member.
example (h : ⊥ ∈ tripleIntersections A B C) : inclusionMinimalIntersectionJoin A B C = ⊥ := by
  apply le_bot_iff.mp
  refine sSup_le fun D hD => ?_
  exact (hD.2 ⊥ h bot_le).ge

-- When both conjugated subgroups are the whole group, the family has just one member.
example : inclusionMinimalIntersectionJoin A ⊤ ⊤ = A := by
  have family (D : Subgroup G) : D ∈ tripleIntersections A ⊤ ⊤ ↔ D = A := by
    simp [tripleIntersections]
  unfold inclusionMinimalIntersectionJoin
  apply le_antisymm
  · apply sSup_le
    intro D hD
    exact ((family D).mp hD.1).le
  · exact le_sSup ⟨(family A).mpr rfl, fun E hE _ => (family E).mp hE⟩
