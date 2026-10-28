/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Prior source equations can be transported linearly and sparse normal forms compared exactly. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorRows
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalRepresentation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Equal checked sparse normal forms denote the same literal binary-module sum. -/
theorem monsterCo1GeometryVectorRowEval_eq_of_normalize {α V : Type*} [DecidableEq α]
    [AddCommGroup V] [Module (ZMod 2) V] (point : α → V) (row target : List α)
    (h : monsterCo1GeometryVectorRowNormalize row =
      monsterCo1GeometryVectorRowNormalize target) :
    monsterCo1GeometryVectorRowEval point row =
      monsterCo1GeometryVectorRowEval point target := by
  rw [← monsterCo1GeometryVectorRowNormalize_eval,
    ← monsterCo1GeometryVectorRowNormalize_eval, h]

/-- Actual linear action transports a prior proved relation when its point images are bound. -/
theorem monsterCo1GeometryVectorRowEval_transport {α V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (point : α → V)
    (L : V →ₗ[ZMod 2] V) (source target : List α)
    (images : target.map point = (source.map point).map L)
    (prior : monsterCo1GeometryVectorRowEval point source = 0) :
    monsterCo1GeometryVectorRowEval point target = 0 := by
  change (target.map point).sum = 0
  rw [images, ← map_list_sum]
  change L (monsterCo1GeometryVectorRowEval point source) = 0
  rw [prior, map_zero]

/-- A zero source row with all remaining points in a subspace places its leading point there. -/
theorem monsterCo1GeometryVectorRowEval_leading_mem {α V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (point : α → V)
    (S : Submodule (ZMod 2) V) (p : α) (row : List α)
    (hrow : ∀ q ∈ row, point q ∈ S)
    (h : monsterCo1GeometryVectorRowEval point (p :: row) = 0) : point p ∈ S := by
  have hr : monsterCo1GeometryVectorRowEval point row ∈ S := by
    apply list_sum_mem
    intro v hv
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
    exact hrow q hq
  change point p + monsterCo1GeometryVectorRowEval point row = 0 at h
  rw [eq_neg_of_add_eq_zero_left h]
  exact S.neg_mem hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
