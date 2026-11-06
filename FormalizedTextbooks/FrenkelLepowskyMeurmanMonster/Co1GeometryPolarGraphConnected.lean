/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarGraphPath

/-! Connectivity of the polar graph on the actual norm-eight Conway geometry points. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Conway action preserves the original point polar graph. -/
theorem monsterCo1PolarGraph_smul (g : Co1) (p q : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryPolarAdjacent p q) :
    monsterCo1GeometryPolarAdjacent (g • p) (g • q) := by
  change co1BinaryPolar (co1BinaryAction g p.val) (co1BinaryAction g q.val) = 1
  rw [co1BinaryPolar_invariant]
  exact h

/-- Every original generator moves the base through genuine polar edges or fixes it. -/
theorem monsterCo1PolarGraph_generator_path (k : Fin 5) :
    Relation.ReflTransGen monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint
      (monsterCo1FiveGenerator k • monsterCo1GeometryBasePoint) := by
  by_cases hk : k = 0
  · subst k
    exact (Relation.ReflTransGen.single monsterCo1PolarPath_edges.1).trans
      (Relation.ReflTransGen.single monsterCo1PolarPath_edges.2)
  · rw [monsterCo1FiveGenerator_fix_base k hk]

/-- Actual group words reachable from the base through polar edges form a submonoid. -/
def monsterCo1GeometryPolarReachableMonoid : Submonoid Co1 where
  carrier := {g | Relation.ReflTransGen monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint
    (g • monsterCo1GeometryBasePoint)}
  one_mem' := by
    change Relation.ReflTransGen monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint
      (1 • monsterCo1GeometryBasePoint)
    rw [one_smul]
  mul_mem' := by
    intro g h hg hh
    change Relation.ReflTransGen monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint
      (g • monsterCo1GeometryBasePoint) at hg
    change Relation.ReflTransGen monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint
      (h • monsterCo1GeometryBasePoint) at hh
    change Relation.ReflTransGen monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint
      ((g * h) • monsterCo1GeometryBasePoint)
    have ht := Relation.ReflTransGen.lift (fun p : MonsterCo1GeometryPoint => g • p)
      (fun p q hpq => monsterCo1PolarGraph_smul g p q hpq) _ _ hh
    exact hg.trans (by simpa only [mul_smul] using ht)

/-- Every actual Conway point is connected to the actual base through genuine polar edges. -/
theorem monsterCo1Geometry_polar_base_connected (p : MonsterCo1GeometryPoint) :
    Relation.ReflTransGen monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint p := by
  have : Finite Co1 := co1_finite
  have h : Submonoid.closure (Set.range monsterCo1FiveGenerator) ≤
      monsterCo1GeometryPolarReachableMonoid := by
    apply Submonoid.closure_le.mpr
    rintro g ⟨k, rfl⟩
    exact monsterCo1PolarGraph_generator_path k
  rw [← Subgroup.closure_toSubmonoid_of_finite, ← monsterCo1FiveSubgroup,
    monsterCo1FiveSubgroup_eq_top] at h
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached p
  have hp := h (show g ∈ (⊤ : Subgroup Co1).toSubmonoid from trivial)
  change Relation.ReflTransGen monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint
    (g • monsterCo1GeometryBasePoint) at hp
  simpa only [hg] using hp

/-- Genuine polar adjacency is symmetric. -/
theorem monsterCo1PolarGraph_symm (p q : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryPolarAdjacent p q) : monsterCo1GeometryPolarAdjacent q p := by
  change qBeta q.val p.val + qBeta p.val q.val = 1
  change qBeta p.val q.val + qBeta q.val p.val = 1 at h
  rwa [add_comm]

/-- Every polar edge path on original geometry points can be reversed. -/
theorem monsterCo1PolarGraph_path_reverse {p q : MonsterCo1GeometryPoint}
    (h : Relation.ReflTransGen monsterCo1GeometryPolarAdjacent p q) :
    Relation.ReflTransGen monsterCo1GeometryPolarAdjacent q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hq ih => exact ih.head (monsterCo1PolarGraph_symm _ _ hq)

/-- The actual Conway geometry point polar graph is connected. -/
theorem monsterCo1Geometry_polar_connected (p q : MonsterCo1GeometryPoint) :
    Relation.ReflTransGen monsterCo1GeometryPolarAdjacent p q :=
  (monsterCo1PolarGraph_path_reverse (monsterCo1Geometry_polar_base_connected p)).trans
    (monsterCo1Geometry_polar_base_connected q)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
