/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Conway projection of local lifts of the source code conjugates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalGenerationMatrixKernel

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Any local lift of the actual y_d has the prescribed actual Conway sign projection.
The existence of this lift remains the full-centralizer obligation. -/
theorem sourceGeneratedY_lift_projection (d : Fin 4096) (ε : ZMod 2) (h : H)
    (hy : localIntoGenerated h = sourceGeneratedY d ε) :
    projH h = (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) := by
  apply projH_eq_of_matrix_action
  intro x
  have hh : rhoLocal h = (sourceGeneratedY d ε).val := congrArg Subtype.val hy
  rw [hh]
  exact sourceGeneratedY_matrix d ε x

/-- A local lift of y_d belongs to the local intersection of any normal subgroup containing Q. -/
theorem sourceGeneratedY_lift_mem_of_q_range_le (N : Subgroup ↥G) [N.Normal]
    (hQ : qIntoGenerated.range ≤ N) (d : Fin 4096) (ε : ZMod 2) (h : H)
    (hy : localIntoGenerated h = sourceGeneratedY d ε) : h ∈ N.comap localIntoGenerated := by
  change localIntoGenerated h ∈ N
  rw [hy]
  exact sourceGeneratedY_mem_of_q_range_le N hQ d ε

/-- The prescribed actual Conway sign belongs to the projection of the local intersection
once the corresponding actual local lift is supplied. -/
theorem sourceGeneratedSign_mem_normal_projection (N : Subgroup ↥G) [N.Normal]
    (hQ : qIntoGenerated.range ≤ N) (d : Fin 4096) (ε : ZMod 2) (h : H)
    (hy : localIntoGenerated h = sourceGeneratedY d ε) :
    (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) ∈
      (N.comap localIntoGenerated).map projH := by
  rw [← sourceGeneratedY_lift_projection d ε h hy]
  exact Subgroup.mem_map_of_mem projH
    (sourceGeneratedY_lift_mem_of_q_range_le N hQ d ε h hy)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
