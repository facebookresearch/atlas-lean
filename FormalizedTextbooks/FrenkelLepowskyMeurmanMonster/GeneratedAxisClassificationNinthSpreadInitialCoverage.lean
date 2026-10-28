/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadInitialPoints

/-! The original nine-system spread covers the full135 norm-eight frame classes of the selected
lattice section. It is not yet identified with the Ninth-axis short marking. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All nonzero classes in the original nine systems are actual section frame classes. -/
theorem generatedNinth_spread_initial_nonzero_subset :
    generatedNinthSpreadInitialNonzero ⊆ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  intro v hv
  obtain ⟨i, hi, hzero⟩ := Set.mem_iUnion.mp hv
  apply (generatedAxisE8ActualFrameSystemCandidate_mem (generatedNinthSpreadInitialIndex i)).2
    v hi
  intro hz
  exact hzero (Set.mem_singleton_iff.mpr hz)

/-- The nine actual systems exhaust all norm-eight frame classes in the original section. -/
theorem generatedNinth_spread_initial_nonzero_eq_frame_classes :
    generatedNinthSpreadInitialNonzero = generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  let : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  apply generatedAxisE8FrameSystems_set_eq_of_subset_card
    _ _ generatedNinth_spread_initial_nonzero_subset
  have he := generatedAxisE8_image_frameClasses_card generatedFifthFlagOctad 1
  change Nat.card (generatedAxisE8FrameClasses (generatedAxisE8SectionEquiv 1
    (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)))) = 135 at he
  rw [generatedAxisE8SectionEquiv_one] at he
  exact generatedNinth_spread_initial_nonzero_card.trans he.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
