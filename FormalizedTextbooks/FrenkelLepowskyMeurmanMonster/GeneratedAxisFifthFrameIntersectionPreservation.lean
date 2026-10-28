/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionImage

/-! Genuine section and Q-image preservation imply preservation of the actual frame system. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Membership in the actual quotient system is membership in its displayed coordinate span. -/
theorem generatedFifthFrameSystem_coordinates (b : LeechModTwo) :
    b ∈ generatedFifthFrameSystem ↔
      leechHyperbolicCoordinates b ∈ generatedFifthFrameSystemBinary := by
  constructor
  · rintro ⟨v, hv, he⟩
    change v ∈ generatedFifthFrameSystemBinary at hv
    rw [← he]
    change leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm v) ∈
      generatedFifthFrameSystemBinary
    simpa only [LinearEquiv.apply_symm_apply] using hv
  · intro hb
    exact Submodule.mem_map.mpr ⟨leechHyperbolicCoordinates b, hb,
      leechHyperbolicCoordinates.symm_apply_apply b⟩

/-- The actual system is the Q image restricted to zero and actual incident norm-eight frames. -/
theorem generatedFifthFrameSystem_mem_iff (b : LeechModTwo) :
    b ∈ generatedFifthFrameSystem ↔
      leechHyperbolicCoordinates b ∈ generatedFifthAxisBinaryImage ∧
        (b = 0 ∨ b ∈ generatedAxisE8FrameClasses
          (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) := by
  constructor
  · intro hb
    refine ⟨((generatedFifthFrameSystemBinary_mem _).mp
      ((generatedFifthFrameSystem_coordinates b).mp hb)).1, ?_⟩
    by_cases hz : b = 0
    · exact Or.inl hz
    · exact Or.inr (generatedFifthFrameSystem_incident b hb hz)
  · rintro ⟨hi, rfl | hf⟩
    · exact Submodule.zero_mem _
    · apply (generatedFifthFrameSystem_coordinates b).mpr
      exact (generatedFifthFrameSystemBinary_mem _).mpr
        ⟨hi, generatedFifthFrame_incident_binary_span b hf⟩

/-- An actual section-preserving isometry preserving the Q image preserves the frame system. -/
theorem generatedFifthFrameSystem_preserved (g : leechIsomSubgroup)
    (hs : generatedAxisE8ImageSection g (golayOctadWord generatedFifthFlagOctad) =
      generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))
    (hi : ∀ v ∈ generatedFifthAxisBinaryImage,
      leechBinaryAction g v ∈ generatedFifthAxisBinaryImage) :
    generatedFifthFrameSystem.map (leechModTwoAction g).toLinearMap =
      generatedFifthFrameSystem := by
  have hle : generatedFifthFrameSystem.map (leechModTwoAction g).toLinearMap ≤
      generatedFifthFrameSystem := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := Submodule.mem_map.mp hb
    rw [← hab]
    apply (generatedFifthFrameSystem_mem_iff _).mpr
    obtain ⟨hai, rfl | haf⟩ := (generatedFifthFrameSystem_mem_iff a).mp ha
    · constructor
      · simpa only [map_zero] using (Submodule.zero_mem generatedFifthAxisBinaryImage)
      · exact Or.inl (map_zero _)
    · refine ⟨?_, Or.inr ?_⟩
      · have he : leechHyperbolicCoordinates (leechModTwoAction g a) =
            leechBinaryAction g (leechHyperbolicCoordinates a) := by
          simp [leechBinaryAction, LinearEquiv.trans_apply]
        change leechHyperbolicCoordinates (leechModTwoAction g a) ∈
          generatedFifthAxisBinaryImage
        rw [he]
        exact hi _ hai
      · have hf := (generatedAxisE8_frame_transport g
          (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) a).mpr haf
        change leechModTwoAction g a ∈ generatedAxisE8FrameClasses
          (generatedAxisE8ImageSection g (golayOctadWord generatedFifthFlagOctad)) at hf
        rwa [hs] at hf
  apply SetLike.coe_injective
  have : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  apply Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle
  exact (Nat.card_congr
    ((leechModTwoAction g).submoduleMap generatedFifthFrameSystem).toEquiv).le

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
