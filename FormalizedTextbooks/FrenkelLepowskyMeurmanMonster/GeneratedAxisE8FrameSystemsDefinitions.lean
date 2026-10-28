/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameFlagsLocal

/-! Genuine fifteen-frame systems: four-dimensional binary subspaces whose nonzero
vectors are all actual norm-eight frame classes incident with the same integral section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine fifteen-frame system is a sixteen-element binary subspace, with each
nonzero vector represented by an actual norm-eight vector in the integral section. -/
def generatedAxisE8FrameSystems (S : Submodule ℤ leechIntegral) :
    Set (Submodule (ZMod 2) LeechModTwo) :=
  {W | Nat.card W = 16 ∧ ∀ b ∈ W, b ≠ 0 → b ∈ generatedAxisE8FrameClasses S}

/-- The literal membership conditions for actual systems, without an abstract frame label. -/
theorem generatedAxisE8FrameSystems_mem (S : Submodule ℤ leechIntegral)
    (W : Submodule (ZMod 2) LeechModTwo) : W ∈ generatedAxisE8FrameSystems S ↔
    Nat.card W = 16 ∧ ∀ b ∈ W, b ≠ 0 → b ∈ generatedAxisE8FrameClasses S := Iff.rfl

/-- Every genuine system contains exactly fifteen nonzero binary frame classes. -/
theorem generatedAxisE8FrameSystems_nonzero_card (S : Submodule ℤ leechIntegral)
    (W : Submodule (ZMod 2) LeechModTwo) (hW : W ∈ generatedAxisE8FrameSystems S) :
    Nat.card {b : W // b ≠ 0} = 15 := by
  classical
  have : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  let : Fintype W := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun b : W => b = 0),
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hW.1]

/-- Actual lattice isometries transport both the integral section and the entire binary system. -/
theorem generatedAxisE8FrameSystems_transport (g : leechIsomSubgroup)
    (S : Submodule ℤ leechIntegral) (W : Submodule (ZMod 2) LeechModTwo) :
    W.map (leechModTwoAction g).toLinearMap ∈
        generatedAxisE8FrameSystems (generatedAxisE8SectionEquiv g S) ↔
      W ∈ generatedAxisE8FrameSystems S := by
  have hcard : Nat.card (W.map (leechModTwoAction g).toLinearMap) = Nat.card W :=
    (Nat.card_congr ((leechModTwoAction g).submoduleMap W).toEquiv).symm
  constructor
  · intro hw
    refine ⟨hcard ▸ hw.1, ?_⟩
    intro b hb hb0
    apply (generatedAxisE8_frame_transport g S b).mp
    apply hw.2
    · exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩
    · intro he
      apply hb0
      exact (leechModTwoAction g).injective (he.trans (map_zero _).symm)
  · intro hw
    refine ⟨hcard.trans hw.1, ?_⟩
    intro b hb hb0
    obtain ⟨a, ha, hab⟩ := Submodule.mem_map.mp hb
    change (leechModTwoAction g) a = b at hab
    have ha0 : a ≠ 0 := by
      intro he
      apply hb0
      rw [← hab, he, map_zero]
    have hf := (generatedAxisE8_frame_transport g S a).mpr (hw.2 a ha ha0)
    rwa [hab] at hf

/-- An actual section-preserving isometry preserves its genuine fifteen-frame systems. -/
theorem generatedAxisE8FrameSystems_section_action (o : Fin 759)
    (g : generatedAxisE8SectionStabilizer (golayOctadWord o))
    (W : Submodule (ZMod 2) LeechModTwo)
    (hW : W ∈ generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    W.map (leechModTwoAction g.val).toLinearMap ∈ generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord o)) := by
  have h := (generatedAxisE8FrameSystems_transport g.val _ W).mpr hW
  change _ ∈ generatedAxisE8FrameSystems (generatedAxisE8ImageSection g.val
    (golayOctadWord o)) at h
  rwa [(generatedAxisE8SectionStabilizer_mem _ g.val).mp g.property] at h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
