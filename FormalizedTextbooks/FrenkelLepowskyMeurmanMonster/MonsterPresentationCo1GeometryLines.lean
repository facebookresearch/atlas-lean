/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Source II §5.1 Conway lines use genuine length-two point-stabilizer two-core orbits. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryPoints

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A source line anchored at p has a genuine Q(p)-orbit consisting of exactly two other points. -/
def monsterCo1GeometryAnchoredLine (p q r : MonsterCo1GeometryPoint) : Prop :=
  p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    MulAction.orbit (monsterCo1GeometryPointTwoCore p) q = {q, r}

/-- The unordered source line predicate permits any of the three actual points as anchor. -/
def monsterCo1GeometryLine (p q r : MonsterCo1GeometryPoint) : Prop :=
  monsterCo1GeometryAnchoredLine p q r ∨ monsterCo1GeometryAnchoredLine q p r ∨
    monsterCo1GeometryAnchoredLine r p q

/-- The two other points on a genuine anchored line lie in the same actual two-core orbit. -/
theorem monsterCo1GeometryAnchoredLine_transport (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryAnchoredLine p q r) :
    ∃ g : monsterCo1GeometryPointTwoCore p, g • q = r := by
  have hr : r ∈ MulAction.orbit (monsterCo1GeometryPointTwoCore p) q := by
    rw [h.2.2.2]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton r)
  exact hr

/-- Exchanging the two points in an actual two-element orbit preserves an anchored source line. -/
theorem monsterCo1GeometryAnchoredLine_swap (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryAnchoredLine p q r) : monsterCo1GeometryAnchoredLine p r q := by
  have hr : r ∈ MulAction.orbit (monsterCo1GeometryPointTwoCore p) q := by
    rw [h.2.2.2]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton r)
  refine ⟨h.2.1, h.1, h.2.2.1.symm, ?_⟩
  rw [(MulAction.orbit_eq_iff).mpr hr, h.2.2.2, Set.pair_comm]

/-- The source line predicate is symmetric in its first two points. -/
theorem monsterCo1GeometryLine_swap_first (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine p q r) : monsterCo1GeometryLine q p r := by
  rcases h with hp | hq | hr
  · exact Or.inr (Or.inl hp)
  · exact Or.inl hq
  · exact Or.inr (Or.inr (monsterCo1GeometryAnchoredLine_swap r p q hr))

/-- The source line predicate is symmetric in its last two points. -/
theorem monsterCo1GeometryLine_swap_last (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine p q r) : monsterCo1GeometryLine p r q := by
  rcases h with hp | hq | hr
  · exact Or.inl (monsterCo1GeometryAnchoredLine_swap p q r hp)
  · exact Or.inr (Or.inr hq)
  · exact Or.inr (Or.inl hr)

/-- Actual anchored lines contain three distinct points. -/
theorem monsterCo1GeometryAnchoredLine_distinct (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryAnchoredLine p q r) : p ≠ q ∧ p ≠ r ∧ q ≠ r :=
  ⟨h.1, h.2.1, h.2.2.1⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
