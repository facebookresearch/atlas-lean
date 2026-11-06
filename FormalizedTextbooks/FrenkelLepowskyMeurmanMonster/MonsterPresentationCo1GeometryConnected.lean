/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine Conway point-line graph is connected through the five actual lattice operators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryFiveQuotient
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBaseCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTetradLine
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLineAction
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Two distinct source points are adjacent precisely when they belong to a genuine source line. -/
def monsterCo1GeometryAdjacent (p q : MonsterCo1GeometryPoint) : Prop :=
  ∃ r, monsterCo1GeometryLine p q r

/-- Actual Conway point-line adjacency transports by genuine Conway action. -/
theorem monsterCo1GeometryAdjacent_smul (g : Co1) (p q : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryAdjacent p q) : monsterCo1GeometryAdjacent (g • p) (g • q) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨g • r, monsterCo1GeometryLine_smul g p q r hr⟩

/-- Every actual non-Xi generator fixes the actual distinguished Conway frame point. -/
theorem monsterCo1FiveGenerator_fix_base (k : Fin 5) (hk : k ≠ 0) :
    monsterCo1FiveGenerator k • monsterCo1GeometryBasePoint = monsterCo1GeometryBasePoint := by
  have hc : ∀ j : Fin 5, j ≠ 0 →
      omegaOrbitBinaryMatrices j *ᵥ (Pi.single 11 (1 : ZMod 2)) = Pi.single 11 1 := by
    decide +kernel
  apply Subtype.ext
  change co1BinaryAction (QuotientGroup.mk (omegaOrbitIsometry k))
    monsterCo1GeometryBasePoint.val = monsterCo1GeometryBasePoint.val
  rw [monsterCo1GeometryBasePoint_binary]
  change leechBinaryAction (omegaOrbitIsometry k) (Pi.single 11 1) = Pi.single 11 1
  rw [omegaOrbitIsometry_binary]
  exact hc k hk

/-- Each actual generator takes the base point to itself or along the proved genuine tetrad line. -/
theorem monsterCo1FiveGenerator_base_path (k : Fin 5) :
    Relation.ReflTransGen monsterCo1GeometryAdjacent monsterCo1GeometryBasePoint
      (monsterCo1FiveGenerator k • monsterCo1GeometryBasePoint) := by
  by_cases hk : k = 0
  · subst k
    obtain ⟨r, hline, _⟩ := monsterCo1GeometryTetradLine_exists
    apply Relation.ReflTransGen.single
    exact ⟨r, Or.inl hline⟩
  · rw [monsterCo1FiveGenerator_fix_base k hk]

/-- Actual group words reachable from the base through genuine lines form a submonoid. -/
def monsterCo1GeometryReachableMonoid : Submonoid Co1 where
  carrier := {g | Relation.ReflTransGen monsterCo1GeometryAdjacent monsterCo1GeometryBasePoint
    (g • monsterCo1GeometryBasePoint)}
  one_mem' := by
    change Relation.ReflTransGen monsterCo1GeometryAdjacent monsterCo1GeometryBasePoint
      (1 • monsterCo1GeometryBasePoint)
    rw [one_smul]
  mul_mem' := by
    intro g h hg hh
    change Relation.ReflTransGen monsterCo1GeometryAdjacent monsterCo1GeometryBasePoint
      (g • monsterCo1GeometryBasePoint) at hg
    change Relation.ReflTransGen monsterCo1GeometryAdjacent monsterCo1GeometryBasePoint
      (h • monsterCo1GeometryBasePoint) at hh
    change Relation.ReflTransGen monsterCo1GeometryAdjacent monsterCo1GeometryBasePoint
      ((g * h) • monsterCo1GeometryBasePoint)
    have ht := Relation.ReflTransGen.lift (fun p : MonsterCo1GeometryPoint => g • p)
      (fun p q hpq => monsterCo1GeometryAdjacent_smul g p q hpq) _ _ hh
    exact hg.trans (by simpa only [mul_smul] using ht)

/-- Every actual Conway point is connected to the actual base through genuine source lines. -/
theorem monsterCo1Geometry_base_connected (p : MonsterCo1GeometryPoint) :
    Relation.ReflTransGen monsterCo1GeometryAdjacent monsterCo1GeometryBasePoint p := by
  have : Finite Co1 := co1_finite
  have h : Submonoid.closure (Set.range monsterCo1FiveGenerator) ≤
      monsterCo1GeometryReachableMonoid := by
    apply Submonoid.closure_le.mpr
    rintro g ⟨k, rfl⟩
    exact monsterCo1FiveGenerator_base_path k
  rw [← Subgroup.closure_toSubmonoid_of_finite, ← monsterCo1FiveSubgroup,
    monsterCo1FiveSubgroup_eq_top] at h
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached p
  have hp := h (show g ∈ (⊤ : Subgroup Co1).toSubmonoid from trivial)
  change Relation.ReflTransGen monsterCo1GeometryAdjacent monsterCo1GeometryBasePoint
    (g • monsterCo1GeometryBasePoint) at hp
  simpa only [hg] using hp

/-- A genuine line path can be reversed using the original source line symmetry. -/
theorem monsterCo1Geometry_path_reverse {p q : MonsterCo1GeometryPoint}
    (h : Relation.ReflTransGen monsterCo1GeometryAdjacent p q) :
    Relation.ReflTransGen monsterCo1GeometryAdjacent q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hq ih =>
      obtain ⟨r, hr⟩ := hq
      exact ih.head ⟨r, monsterCo1GeometryLine_swap_first _ _ _ hr⟩

/-- The actual Conway point-line graph is connected; every edge is an original genuine line. -/
theorem monsterCo1Geometry_connected (p q : MonsterCo1GeometryPoint) :
    Relation.ReflTransGen monsterCo1GeometryAdjacent p q :=
  (monsterCo1Geometry_path_reverse (monsterCo1Geometry_base_connected p)).trans
    (monsterCo1Geometry_base_connected q)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
