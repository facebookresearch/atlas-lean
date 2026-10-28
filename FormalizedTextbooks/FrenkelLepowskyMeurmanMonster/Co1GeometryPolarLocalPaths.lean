/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalPathBindings

/-! Nine genuine line transports supply paths for all four base-stabilizer generators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The standard genuine pentad bundled in the actual base polar-neighbor set. -/
def monsterCo1PolarLocalPentad :
    {p : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent
      monsterCo1GeometryBasePoint p} :=
  ⟨monsterCo1PolarPentadPoint, monsterCo1PolarPentadPoint_neighbor⟩

/-- Each original base-fixing generator image remains in the genuine polar-neighbor set. -/
def monsterCo1PolarLocalGeneratorPoint (k : Fin 4) :
    {p : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent
      monsterCo1GeometryBasePoint p} :=
  ⟨monsterCo1FiveGenerator k.succ • monsterCo1PolarPentadPoint, by
    have h := monsterCo1PolarGraph_smul (monsterCo1FiveGenerator k.succ)
      monsterCo1GeometryBasePoint monsterCo1PolarPentadPoint monsterCo1PolarPentadPoint_neighbor
    rw [monsterCo1FiveGenerator_fix_base k.succ (by simp)] at h
    exact h⟩

/-- The first source edge of each of the four generator paths. -/
def monsterCo1PolarLocalStartEdge : Fin 4 → Fin 9 := ![0, 2, 4, 6]

/-- The last source edge, oriented back from each generator image. -/
def monsterCo1PolarLocalFinishEdge : Fin 4 → Fin 9 := ![1, 3, 5, 8]

/-- Every path starts at the actual standard pentad point, by complete binary endpoint binding. -/
theorem monsterCo1PolarLocal_start (k : Fin 4) :
    monsterCo1PolarLocalEdgeBase (monsterCo1PolarLocalStartEdge k) =
      monsterCo1PolarLocalPentad := by
  apply Subtype.ext
  apply Subtype.ext
  change (monsterCo1PolarLocalEdgeWord (monsterCo1PolarLocalStartEdge k) •
    monsterCo1GeometryBasePoint).val = monsterCo1PolarPentadPoint.val
  rw [monsterCo1PolarLocalEdge_base_binary, monsterCo1PolarPentadPoint_binary]
  revert k
  decide +kernel

/-- Every path ends at the literal original-generator image of the actual pentad point. -/
theorem monsterCo1PolarLocal_finish (k : Fin 4) :
    monsterCo1PolarLocalEdgeBase (monsterCo1PolarLocalFinishEdge k) =
      monsterCo1PolarLocalGeneratorPoint k := by
  apply Subtype.ext
  apply Subtype.ext
  change (monsterCo1PolarLocalEdgeWord (monsterCo1PolarLocalFinishEdge k) •
    monsterCo1GeometryBasePoint).val =
      co1BinaryAction (monsterCo1FiveGenerator k.succ) monsterCo1PolarPentadPoint.val
  rw [monsterCo1PolarLocalEdge_base_binary, monsterCo1PolarPentadPoint_binary,
    monsterCo1PolarLocal_generator_matrix]
  revert k
  decide +kernel

/-- The two-edge paths join at the same actual intermediate points. -/
theorem monsterCo1PolarLocal_short_joins :
    monsterCo1PolarLocalEdgeTip 0 = monsterCo1PolarLocalEdgeTip 1 ∧
    monsterCo1PolarLocalEdgeTip 2 = monsterCo1PolarLocalEdgeTip 3 ∧
    monsterCo1PolarLocalEdgeTip 4 = monsterCo1PolarLocalEdgeTip 5 := by
  have hj (a b : Fin 9) (h : monsterCo1PolarLocalEdgeTipMasks a =
      monsterCo1PolarLocalEdgeTipMasks b) :
      monsterCo1PolarLocalEdgeTip a = monsterCo1PolarLocalEdgeTip b := by
    apply Subtype.ext
    apply Subtype.ext
    change (monsterCo1PolarLocalEdgeWord a • monsterCo1GeometryTetradPoint).val =
      (monsterCo1PolarLocalEdgeWord b • monsterCo1GeometryTetradPoint).val
    rw [monsterCo1PolarLocalEdge_tip_binary, monsterCo1PolarLocalEdge_tip_binary, h]
  exact ⟨hj 0 1 rfl, hj 2 3 rfl, hj 4 5 rfl⟩

/-- Both intermediate joins of the genuine three-edge last-generator path. -/
theorem monsterCo1PolarLocal_long_joins :
    monsterCo1PolarLocalEdgeTip 6 = monsterCo1PolarLocalEdgeBase 7 ∧
      monsterCo1PolarLocalEdgeTip 7 = monsterCo1PolarLocalEdgeTip 8 := by
  constructor
  · apply Subtype.ext
    apply Subtype.ext
    change (monsterCo1PolarLocalEdgeWord 6 • monsterCo1GeometryTetradPoint).val =
      (monsterCo1PolarLocalEdgeWord 7 • monsterCo1GeometryBasePoint).val
    rw [monsterCo1PolarLocalEdge_tip_binary, monsterCo1PolarLocalEdge_base_binary]
    rfl
  · apply Subtype.ext
    apply Subtype.ext
    change (monsterCo1PolarLocalEdgeWord 7 • monsterCo1GeometryTetradPoint).val =
      (monsterCo1PolarLocalEdgeWord 8 • monsterCo1GeometryTetradPoint).val
    rw [monsterCo1PolarLocalEdge_tip_binary, monsterCo1PolarLocalEdge_tip_binary]
    rfl

/-- Every original base-fixing generator has a genuine-line path inside the actual neighborhood. -/
theorem monsterCo1PolarLocal_generator_path (k : Fin 4) :
    Relation.ReflTransGen (fun u v => monsterCo1GeometryAdjacent u.val v.val)
      monsterCo1PolarLocalPentad (monsterCo1PolarLocalGeneratorPoint k) := by
  rw [← monsterCo1PolarLocal_start k, ← monsterCo1PolarLocal_finish k]
  fin_cases k
  · have h : Relation.ReflTransGen
        (fun u v => monsterCo1GeometryAdjacent u.val v.val)
        (monsterCo1PolarLocalEdgeBase 0) (monsterCo1PolarLocalEdgeTip 0) :=
      Relation.ReflTransGen.single (monsterCo1PolarLocalEdge_adjacent 0)
    rw [monsterCo1PolarLocal_short_joins.1] at h
    exact h.trans (Relation.ReflTransGen.single (monsterCo1PolarLocalEdge_adjacent_reverse 1))
  · have h : Relation.ReflTransGen
        (fun u v => monsterCo1GeometryAdjacent u.val v.val)
        (monsterCo1PolarLocalEdgeBase 2) (monsterCo1PolarLocalEdgeTip 2) :=
      Relation.ReflTransGen.single (monsterCo1PolarLocalEdge_adjacent 2)
    rw [monsterCo1PolarLocal_short_joins.2.1] at h
    exact h.trans (Relation.ReflTransGen.single (monsterCo1PolarLocalEdge_adjacent_reverse 3))
  · have h : Relation.ReflTransGen
        (fun u v => monsterCo1GeometryAdjacent u.val v.val)
        (monsterCo1PolarLocalEdgeBase 4) (monsterCo1PolarLocalEdgeTip 4) :=
      Relation.ReflTransGen.single (monsterCo1PolarLocalEdge_adjacent 4)
    rw [monsterCo1PolarLocal_short_joins.2.2] at h
    exact h.trans (Relation.ReflTransGen.single (monsterCo1PolarLocalEdge_adjacent_reverse 5))
  · have h : Relation.ReflTransGen
        (fun u v => monsterCo1GeometryAdjacent u.val v.val)
        (monsterCo1PolarLocalEdgeBase 6) (monsterCo1PolarLocalEdgeTip 6) :=
      Relation.ReflTransGen.single (monsterCo1PolarLocalEdge_adjacent 6)
    rw [monsterCo1PolarLocal_long_joins.1] at h
    have h2 : Relation.ReflTransGen
        (fun u v => monsterCo1GeometryAdjacent u.val v.val)
        (monsterCo1PolarLocalEdgeBase 7) (monsterCo1PolarLocalEdgeTip 7) :=
      Relation.ReflTransGen.single (monsterCo1PolarLocalEdge_adjacent 7)
    rw [monsterCo1PolarLocal_long_joins.2] at h2
    exact (h.trans h2).trans
      (Relation.ReflTransGen.single (monsterCo1PolarLocalEdge_adjacent_reverse 8))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
