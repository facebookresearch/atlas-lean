/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionNormEightData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationE8Transport

/-! The fifteen displayed classes are genuine norm-eight frames
inside the actual selected section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual norm-eight lattice representatives recovered from their literal integer coordinates. -/
def generatedFifthFrameNormEightVector (j : Fin 15) : leechIntegral :=
  leechExplicitCoordinates.symm (generatedFifthFrameNormEightInteger.col j)

/-- The constructed lattice vectors have their exact displayed physical coordinates. -/
theorem generatedFifthFrameNormEightVector_physical (j : Fin 15) :
    (generatedFifthFrameNormEightVector j).val = generatedFifthFrameNormEightPhysical.col j := by
  have h := leechExplicitCoordinates_vector (generatedFifthFrameNormEightVector j)
  rw [generatedFifthFrameNormEightVector, LinearEquiv.apply_symm_apply] at h
  exact h.symm.trans (generatedFifthFrame_norm_eight_physical_certificate j)

/-- Each literal lattice representative has genuine norm eight. -/
theorem generatedFifthFrameNormEightVector_square (j : Fin 15) :
    leechSquareSum (generatedFifthFrameNormEightVector j).val = 64 := by
  rw [generatedFifthFrameNormEightVector_physical]
  exact generatedFifthFrame_norm_eight_square_certificate j

/-- Each literal lattice representative belongs to the actual selected coordinate section. -/
theorem generatedFifthFrameNormEightVector_supported (j : Fin 15) :
    generatedOctadSupported (golayOctadWord generatedFifthFlagOctad)
      (generatedFifthFrameNormEightVector j).val := by
  rw [generatedFifthFrameNormEightVector_physical]
  exact generatedFifthFrame_norm_eight_support_certificate j

/-- Each displayed binary class is the quotient class of its actual lattice representative. -/
theorem generatedFifthFrameNormEightVector_binary (j : Fin 15) :
    leechHyperbolicCoordinates (leechReduction (generatedFifthFrameNormEightVector j)) =
      generatedFifthFrameIncidentClass j := by
  rw [leechHyperbolicCoordinates_explicit, generatedFifthFrameNormEightVector,
    LinearEquiv.apply_symm_apply]
  exact generatedFifthFrame_norm_eight_binary_certificate j

/-- Every displayed class is a genuine norm-eight frame incident with the selected section. -/
theorem generatedFifthFrameIncidentClass_mem (j : Fin 15) :
    leechHyperbolicCoordinates.symm (generatedFifthFrameIncidentClass j) ∈
      generatedAxisE8FrameClasses
        (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  refine ⟨generatedFifthFrameNormEightVector j,
    generatedFifthFrameNormEightVector_supported j,
    generatedFifthFrameNormEightVector_square j, ?_⟩
  apply leechHyperbolicCoordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  exact generatedFifthFrameNormEightVector_binary j

/-- The displayed fifteen genuine incident classes are nonzero. -/
theorem generatedFifthFrameIncidentClass_ne_zero : ∀ j : Fin 15,
    generatedFifthFrameIncidentClass j ≠ 0 := by
  decide +kernel

/-- The displayed actual incident frame set has exactly fifteen classes. -/
theorem generatedFifthFrameIncidentClass_range_card :
    Nat.card (Set.range generatedFifthFrameIncidentClass) = 15 := by
  rw [← Nat.card_congr (Equiv.ofInjective generatedFifthFrameIncidentClass
    generatedFifthFrameIncidentClass_injective)]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
