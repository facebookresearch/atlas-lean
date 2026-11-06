/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1UniversalPolarCommutatorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLineAction

/-! Genuine-line local connectivity transports through the actual Conway point action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Conway action identifies the corresponding polar-neighbor sets. -/
def monsterCo1PolarNeighborEquiv (g : Co1) (x : MonsterCo1GeometryPoint) :
    {y : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent x y} ≃
      {y : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent (g • x) y} where
  toFun y := ⟨g • y.val, monsterCo1PolarGraph_smul g x y.val y.property⟩
  invFun y := ⟨g⁻¹ • y.val, by
    have h := monsterCo1PolarGraph_smul g⁻¹ (g • x) y.val y.property
    simpa only [inv_smul_smul] using h⟩
  left_inv y := Subtype.ext (inv_smul_smul g y.val)
  right_inv y := Subtype.ext (smul_inv_smul g y.val)

/-- Actual polar-neighbor equivalences transport every genuine-line edge. -/
theorem monsterCo1PolarNeighborEquiv_adjacent (g : Co1) (x : MonsterCo1GeometryPoint)
    (u v : {y : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent x y})
    (h : monsterCo1GeometryAdjacent u.val v.val) :
    monsterCo1GeometryAdjacent (monsterCo1PolarNeighborEquiv g x u).val
      (monsterCo1PolarNeighborEquiv g x v).val :=
  monsterCo1GeometryAdjacent_smul g u.val v.val h

/-- Local genuine-line connectivity at the actual base point implies it at every actual point. -/
theorem monsterCo1PolarLocalConnected_of_base
    (hbase : ∀ u v : {y : MonsterCo1GeometryPoint //
      monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint y},
      Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val) u v) :
    monsterCo1PolarLocalConnected := by
  intro x u v
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached x
  subst x
  let e := monsterCo1PolarNeighborEquiv g monsterCo1GeometryBasePoint
  have h := hbase (e.symm u) (e.symm v)
  have ht := Relation.ReflTransGen.lift (p :=
      fun a b : {y : MonsterCo1GeometryPoint //
        monsterCo1GeometryPolarAdjacent (g • monsterCo1GeometryBasePoint) y} =>
          monsterCo1GeometryAdjacent a.val b.val) e
    (fun a b hab => monsterCo1PolarNeighborEquiv_adjacent g
      monsterCo1GeometryBasePoint a b hab) _ _ h
  change Relation.ReflTransGen (fun a b => monsterCo1GeometryAdjacent a.val b.val)
    (e (e.symm u)) (e (e.symm v)) at ht
  simpa only [Equiv.apply_symm_apply] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
