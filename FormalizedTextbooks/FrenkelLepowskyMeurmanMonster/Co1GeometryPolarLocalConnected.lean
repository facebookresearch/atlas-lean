/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalPaths

/-! Actual local connectivity through original genuine lines in every polar neighborhood. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual full monomial stabilizer acts inside the base polar-neighbor carrier. -/
def monsterCo1PolarLocalMonomialAction (g : monsterCo1GeometryMonomialClasses)
    (u : {p : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent
      monsterCo1GeometryBasePoint p}) :
    {p : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent
      monsterCo1GeometryBasePoint p} :=
  ⟨g.val • u.val, by
    have hg : g.val • monsterCo1GeometryBasePoint = monsterCo1GeometryBasePoint :=
      by
        have hm : g.val ∈ monsterCo1GeometryPointStabilizer
            monsterCo1GeometryBasePoint := by
          rw [monsterCo1GeometryBasePoint_stabilizer]
          exact g.property
        exact hm
    have h := monsterCo1PolarGraph_smul g.val monsterCo1GeometryBasePoint u.val u.property
    rw [hg] at h
    exact h⟩

/-- The genuine restricted monomial action has the actual identity law. -/
theorem monsterCo1PolarLocalMonomialAction_one (u) :
    monsterCo1PolarLocalMonomialAction 1 u = u := Subtype.ext (one_smul Co1 u.val)

/-- The genuine restricted monomial action has the actual multiplication law. -/
theorem monsterCo1PolarLocalMonomialAction_mul (g h : monsterCo1GeometryMonomialClasses) (u) :
    monsterCo1PolarLocalMonomialAction (g * h) u =
      monsterCo1PolarLocalMonomialAction g (monsterCo1PolarLocalMonomialAction h u) :=
  Subtype.ext (mul_smul g.val h.val u.val)

/-- Original four generators bundled in the actual full base-point stabilizer. -/
def monsterCo1PolarLocalMonomialGenerator (k : Fin 4) : monsterCo1GeometryMonomialClasses :=
  ⟨monsterCo1FiveGenerator k.succ, by
    rw [← monsterCo1PolarLocalFourSubgroup_eq_monomial]
    exact Subgroup.subset_closure ⟨k, rfl⟩⟩

/-- The four actual bundled generators generate the whole actual base-point stabilizer. -/
theorem monsterCo1PolarLocalMonomialGenerator_closure :
    Subgroup.closure (Set.range monsterCo1PolarLocalMonomialGenerator) = ⊤ := by
  let P := Subgroup.closure (Set.range monsterCo1PolarLocalMonomialGenerator)
  have hmap : P.map monsterCo1GeometryMonomialClasses.subtype =
      monsterCo1GeometryMonomialClasses := by
    dsimp only [P]
    rw [MonoidHom.map_closure, ← Set.range_comp]
    change monsterCo1PolarLocalFourSubgroup = monsterCo1GeometryMonomialClasses
    exact monsterCo1PolarLocalFourSubgroup_eq_monomial
  apply top_unique
  intro g _
  have hg : g.val ∈ P.map monsterCo1GeometryMonomialClasses.subtype := by
    rw [hmap]
    exact g.property
  obtain ⟨h, hh, he⟩ := hg
  have hhe : h = g := Subtype.ext he
  exact hhe ▸ hh

/-- Reachable actual monomial elements form a submonoid using genuine-line transport. -/
def monsterCo1PolarLocalReachableMonoid : Submonoid monsterCo1GeometryMonomialClasses where
  carrier := {g | Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val)
    monsterCo1PolarLocalPentad (monsterCo1PolarLocalMonomialAction g monsterCo1PolarLocalPentad)}
  one_mem' := by
    change Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val)
      monsterCo1PolarLocalPentad
      (monsterCo1PolarLocalMonomialAction 1 monsterCo1PolarLocalPentad)
    rw [monsterCo1PolarLocalMonomialAction_one]
  mul_mem' := by
    intro g h hg hh
    change Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val)
      monsterCo1PolarLocalPentad (monsterCo1PolarLocalMonomialAction g monsterCo1PolarLocalPentad)
        at hg
    change Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val)
      monsterCo1PolarLocalPentad (monsterCo1PolarLocalMonomialAction h monsterCo1PolarLocalPentad)
        at hh
    change Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val)
      monsterCo1PolarLocalPentad (monsterCo1PolarLocalMonomialAction (g * h)
        monsterCo1PolarLocalPentad)
    have ht := Relation.ReflTransGen.lift (p := fun u v =>
      monsterCo1GeometryAdjacent u.val v.val) (monsterCo1PolarLocalMonomialAction g)
      (fun u v huv => monsterCo1GeometryAdjacent_smul g.val u.val v.val huv) _ _ hh
    have h := hg.trans ht
    rw [monsterCo1PolarLocalMonomialAction_mul]
    exact h

/-- Every actual base polar neighbor is reached from the pentad by genuine local lines. -/
theorem monsterCo1PolarLocal_base_reached
    (u : {p : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent
      monsterCo1GeometryBasePoint p}) :
    Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val)
      monsterCo1PolarLocalPentad u := by
  have : Finite Co1 := co1_finite
  have h : Submonoid.closure (Set.range monsterCo1PolarLocalMonomialGenerator) ≤
      monsterCo1PolarLocalReachableMonoid := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨k, rfl⟩
    exact monsterCo1PolarLocal_generator_path k
  rw [← Subgroup.closure_toSubmonoid_of_finite, monsterCo1PolarLocalMonomialGenerator_closure] at h
  obtain ⟨g, hg, hgu⟩ := monsterCo1PolarLocal_neighbor_monomial u.val u.property
  let a : monsterCo1GeometryMonomialClasses := ⟨g, hg⟩
  have hu : monsterCo1PolarLocalMonomialAction a⁻¹ monsterCo1PolarLocalPentad = u := by
    apply Subtype.ext
    change g⁻¹ • monsterCo1PolarPentadPoint = u.val
    rw [← hgu, inv_smul_smul]
  have hp := h (show a⁻¹ ∈
    (⊤ : Subgroup monsterCo1GeometryMonomialClasses).toSubmonoid from trivial)
  change Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val)
    monsterCo1PolarLocalPentad (monsterCo1PolarLocalMonomialAction a⁻¹ monsterCo1PolarLocalPentad)
        at hp
  rw [hu] at hp
  exact hp

/-- A genuine local path reverses inside the same actual polar-neighbor set. -/
theorem monsterCo1PolarLocal_reverse {u v : {p : MonsterCo1GeometryPoint //
    monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint p}}
    (h : Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val) u v) :
    Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ he ih =>
    obtain ⟨r, hr⟩ := he
    exact ih.head ⟨r, monsterCo1GeometryLine_swap_first _ _ _ hr⟩

/-- Every actual base polar-neighbor set is connected through original genuine source lines. -/
theorem monsterCo1PolarLocal_base_connected (u v : {p : MonsterCo1GeometryPoint //
    monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint p}) :
    Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val) u v :=
  (monsterCo1PolarLocal_reverse (monsterCo1PolarLocal_base_reached u)).trans
    (monsterCo1PolarLocal_base_reached v)

/-- Actual local polar-neighbor connectivity, with every edge an original genuine source line. -/
theorem monsterCo1Geometry_polar_local_connected : monsterCo1PolarLocalConnected :=
  monsterCo1PolarLocalConnected_of_base monsterCo1PolarLocal_base_connected

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
