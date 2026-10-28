/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagFramesCountWitnesses

/-! Sixty-three distinct actual quotient frames in the exact fourth-flag generator orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each actual witness class is reached from the base frame by an element of the exact closure. -/
theorem generatedFourthFlagFramesCount_class_mem_orbit (j : Fin 63) :
    generatedFourthFlagFramesCountClass j ∈
      MulAction.orbit generatedFourthPhysicalFlagGeneratorSubgroup
        (leechReduction (leechCoordinateFrameLattice 0)) := by
  let e : generatedFourthPhysicalFlagGeneratorSubgroup :=
    ⟨generatedFourthFlagFramesCountIsometry j, generatedFourthFlagFramesCount_isometry_mem j⟩
  refine ⟨e, ?_⟩
  change leechModTwoAction (generatedFourthFlagFramesCountIsometry j)
    (leechReduction (leechCoordinateFrameLattice 0)) = _
  rw [← leechFrame_reduction_eq 8]
  rfl

/-- The 63 explicit actual reductions, bundled in the exact generator orbit. -/
def generatedFourthFlagFramesCountOrbitMap (j : Fin 63) :
    MulAction.orbit generatedFourthPhysicalFlagGeneratorSubgroup
      (leechReduction (leechCoordinateFrameLattice 0)) :=
  ⟨generatedFourthFlagFramesCountClass j, generatedFourthFlagFramesCount_class_mem_orbit j⟩

/-- The actual orbit contains all 63 distinct checked quotient classes. -/
theorem generatedFourthFlagFramesCount_orbitMap_injective :
    Function.Injective generatedFourthFlagFramesCountOrbitMap := by
  intro i j h
  exact generatedFourthFlagFramesCount_class_injective (congrArg Subtype.val h)

/-- The exact fourth-flag generator subgroup has at least 63 frames in its genuine base orbit. -/
theorem generatedFourthFlagFramesCount_orbit_lower :
    63 ≤ Nat.card (MulAction.orbit generatedFourthPhysicalFlagGeneratorSubgroup
      (leechReduction (leechCoordinateFrameLattice 0))) := by
  let : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  have h := Nat.card_le_card_of_injective generatedFourthFlagFramesCountOrbitMap
    generatedFourthFlagFramesCount_orbitMap_injective
  simpa only [Nat.card_fin] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
