/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsIncidence

/-! Genuine fifteen-frame systems and intrinsic totally singular four-spaces have
exactly the same carrier under the actual root embedding. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sixteen-element subspaces which are totally singular for the intrinsic E8 form. -/
def generatedAxisE8IntrinsicFrameSystems : Set (Submodule (ZMod 2) (Fin 8 → ZMod 2)) :=
  {V | Nat.card V = 16 ∧ ∀ a ∈ V, generatedAxisE8FrameQuadratic a = 0}

/-- The actual root embedding preserves the cardinality of every intrinsic subspace. -/
theorem generatedAxisE8FrameRootEmbedding_map_card
    (V : Submodule (ZMod 2) (Fin 8 → ZMod 2)) :
    Nat.card (V.map generatedAxisE8FrameRootEmbedding) = Nat.card V :=
  (Nat.card_congr (Submodule.equivMapOfInjective generatedAxisE8FrameRootEmbedding
    generatedAxisE8FrameRootEmbedding_injective V).toEquiv).symm

/-- Every intrinsic totally singular four-space is an actual fifteen-frame system. -/
theorem generatedAxisE8IntrinsicFrameSystems_map (V : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hV : V ∈ generatedAxisE8IntrinsicFrameSystems) :
    V.map generatedAxisE8FrameRootEmbedding ∈ generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  refine ⟨(generatedAxisE8FrameRootEmbedding_map_card V).trans hV.1, ?_⟩
  intro b hb hb0
  obtain ⟨a, ha, hab⟩ := Submodule.mem_map.mp hb
  have ha0 : a ≠ 0 := by intro hz; apply hb0; rw [← hab, hz, map_zero]
  rw [← hab]
  exact generatedAxisE8Frame_singular_incident a ha0 (hV.2 a ha)

/-- Every actual system lies in the genuine eight-root binary range. -/
theorem generatedAxisE8FrameSystems_le_root_range
    (W : Submodule (ZMod 2) LeechModTwo)
    (hW : W ∈ generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) :
    W ≤ generatedAxisE8FrameRootEmbedding.range := by
  intro b hb
  by_cases hb0 : b = 0
  · rw [hb0]; exact Submodule.zero_mem _
  · obtain ⟨a, _, _, ha⟩ := generatedAxisE8Frame_incident_singular b (hW.2 b hb hb0)
    exact ⟨a, ha⟩

/-- Mapping the intrinsic preimage recovers the entire actual fifteen-frame system. -/
theorem generatedAxisE8FrameSystems_map_comap
    (W : Submodule (ZMod 2) LeechModTwo)
    (hW : W ∈ generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) :
    (W.comap generatedAxisE8FrameRootEmbedding).map generatedAxisE8FrameRootEmbedding = W := by
  apply le_antisymm
  · exact Submodule.map_comap_le _ _
  · intro b hb
    obtain ⟨a, ha⟩ := generatedAxisE8FrameSystems_le_root_range W hW hb
    apply Submodule.mem_map.mpr
    refine ⟨a, ?_, ha⟩
    change generatedAxisE8FrameRootEmbedding a ∈ W
    rwa [ha]

/-- Every actual fifteen-frame system pulls back to an intrinsic totally singular four-space. -/
theorem generatedAxisE8FrameSystems_comap (W : Submodule (ZMod 2) LeechModTwo)
    (hW : W ∈ generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) :
    W.comap generatedAxisE8FrameRootEmbedding ∈ generatedAxisE8IntrinsicFrameSystems := by
  have hc := generatedAxisE8FrameRootEmbedding_map_card (W.comap generatedAxisE8FrameRootEmbedding)
  rw [generatedAxisE8FrameSystems_map_comap W hW] at hc
  refine ⟨hc.symm.trans hW.1, ?_⟩
  intro a ha
  by_cases ha0 : a = 0
  · rw [ha0]; simp [generatedAxisE8FrameQuadratic]
  · have he0 : generatedAxisE8FrameRootEmbedding a ≠ 0 := by
      intro he
      exact ha0 (generatedAxisE8FrameRootEmbedding_injective (he.trans (map_zero _).symm))
    exact ((generatedAxisE8Frame_incident_iff a).mp (hW.2 _ ha he0)).2

/-- The actual frame-system carrier is equivalent to the intrinsic four-space carrier. -/
def generatedAxisE8FrameSystemsEquiv : generatedAxisE8IntrinsicFrameSystems ≃
    generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) where
  toFun V := ⟨V.val.map generatedAxisE8FrameRootEmbedding,
    generatedAxisE8IntrinsicFrameSystems_map V.val V.property⟩
  invFun W := ⟨W.val.comap generatedAxisE8FrameRootEmbedding,
    generatedAxisE8FrameSystems_comap W.val W.property⟩
  left_inv V := Subtype.ext (Submodule.comap_map_eq_of_injective
    generatedAxisE8FrameRootEmbedding_injective V.val)
  right_inv W := Subtype.ext (generatedAxisE8FrameSystems_map_comap W.val W.property)

/-- Counts of genuine systems are exactly counts of intrinsic totally singular four-spaces. -/
theorem generatedAxisE8FrameSystems_card_intrinsic :
    Nat.card (generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) =
    Nat.card generatedAxisE8IntrinsicFrameSystems :=
  (Nat.card_congr generatedAxisE8FrameSystemsEquiv).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
