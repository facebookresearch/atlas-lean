/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalPathData

/-! Cached complete binary word actions are bound to original genuine line endpoints. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original transporter has exactly its recorded complete actual base-point image. -/
theorem monsterCo1PolarLocalEdge_base_binary (e : Fin 9) :
    (monsterCo1PolarLocalEdgeWord e • monsterCo1GeometryBasePoint).val =
      co1IrreducibleBitVector (monsterCo1PolarLocalEdgeBaseMasks e) := by
  have h := monsterCo1PolarLocalTrace_sound 2048 _
    (monsterCo1PolarLocalEdgeTrace_certificate e).1
  rw [(monsterCo1PolarLocalEdgeTrace_final e).1] at h
  simp only [List.map_map, Function.comp_def] at h
  change co1BinaryAction (monsterCo1PolarLocalEdgeWord e) monsterCo1GeometryBasePoint.val = _
  rw [monsterCo1GeometryBasePoint_binary]
  have hb : (Pi.single 11 1 : Fin 24 → ZMod 2) = co1IrreducibleBitVector 2048 := by
    decide +kernel
  rw [hb]
  exact h

/-- Every original transporter has exactly its recorded complete actual tetrad-point image. -/
theorem monsterCo1PolarLocalEdge_tip_binary (e : Fin 9) :
    (monsterCo1PolarLocalEdgeWord e • monsterCo1GeometryTetradPoint).val =
      co1IrreducibleBitVector (monsterCo1PolarLocalEdgeTipMasks e) := by
  have h := monsterCo1PolarLocalTrace_sound 4194304 _
    (monsterCo1PolarLocalEdgeTrace_certificate e).2
  rw [(monsterCo1PolarLocalEdgeTrace_final e).2] at h
  simp only [List.map_map, Function.comp_def] at h
  change co1BinaryAction (monsterCo1PolarLocalEdgeWord e) monsterCo1GeometryTetradPoint.val = _
  rw [monsterCo1PolarLocal_tetrad_binary]
  exact h

/-- Every recorded base image is inside the actual base polar neighborhood. -/
theorem monsterCo1PolarLocalEdge_base_neighbor (e : Fin 9) :
    monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint
      (monsterCo1PolarLocalEdgeWord e • monsterCo1GeometryBasePoint) := by
  change co1BinaryPolar monsterCo1GeometryBasePoint.val _ = 1
  rw [monsterCo1PolarBase_apply, monsterCo1PolarLocalEdge_base_binary]
  revert e
  decide +kernel

/-- Every recorded tetrad image is inside the same actual base polar neighborhood. -/
theorem monsterCo1PolarLocalEdge_tip_neighbor (e : Fin 9) :
    monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint
      (monsterCo1PolarLocalEdgeWord e • monsterCo1GeometryTetradPoint) := by
  change co1BinaryPolar monsterCo1GeometryBasePoint.val _ = 1
  rw [monsterCo1PolarBase_apply, monsterCo1PolarLocalEdge_tip_binary]
  revert e
  decide +kernel

/-- The transported base endpoint, bundled in the genuine polar neighborhood. -/
def monsterCo1PolarLocalEdgeBase (e : Fin 9) :
    {p : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent
      monsterCo1GeometryBasePoint p} :=
  ⟨monsterCo1PolarLocalEdgeWord e • monsterCo1GeometryBasePoint,
    monsterCo1PolarLocalEdge_base_neighbor e⟩

/-- The transported tetrad endpoint in the same genuine polar neighborhood. -/
def monsterCo1PolarLocalEdgeTip (e : Fin 9) :
    {p : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent
      monsterCo1GeometryBasePoint p} :=
  ⟨monsterCo1PolarLocalEdgeWord e • monsterCo1GeometryTetradPoint,
    monsterCo1PolarLocalEdge_tip_neighbor e⟩

/-- Each local edge is a translate of the already proved genuine source tetrad line. -/
theorem monsterCo1PolarLocalEdge_adjacent (e : Fin 9) :
    monsterCo1GeometryAdjacent (monsterCo1PolarLocalEdgeBase e).val
      (monsterCo1PolarLocalEdgeTip e).val := by
  obtain ⟨r, hr, _⟩ := monsterCo1GeometryTetradLine_exists
  exact monsterCo1GeometryAdjacent_smul (monsterCo1PolarLocalEdgeWord e) _ _ ⟨r, Or.inl hr⟩

/-- Every proved genuine local edge also has its reversed orientation. -/
theorem monsterCo1PolarLocalEdge_adjacent_reverse (e : Fin 9) :
    monsterCo1GeometryAdjacent (monsterCo1PolarLocalEdgeTip e).val
      (monsterCo1PolarLocalEdgeBase e).val := by
  obtain ⟨r, hr⟩ := monsterCo1PolarLocalEdge_adjacent e
  exact ⟨r, monsterCo1GeometryLine_swap_first _ _ _ hr⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
