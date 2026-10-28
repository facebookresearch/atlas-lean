/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingTrialitySquareCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionReversibility

/-! Genuine cocode reflection between the two original containing coordinate phase prototypes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Every odd original cocode fixes every entire original minus-pair axis. -/
theorem generatedFeasibleContaining_odd_cocode_first_fixed (h : SpinIndex)
    (hh : h 11 = 1) (p : Fin 276) :
    rhoLocal (inclQ (cocodeQ h)) (conwayAxis p) = conwayAxis p := by
  apply trialityBlocksEquiv.injective
  rw [cocodeQ_blocks h hh, conwayAxis_blocks]
  ext <;> simp [cocodeDictionaryAction, conwayAxisBlocks]

/-- A vanishing genuine cocode phase fixes the entire original signed short axis. -/
theorem generatedFeasibleContaining_cocode_short_fixed (h : SpinIndex)
    (r : GriessShortIndex) (c : ZMod 2)
    (hp : spinDot h (spinTranslation (griessShortQ r)) = 0) :
    rhoLocal (inclQ (cocodeQ h)) (conwayShortAxis r c) = conwayShortAxis r c := by
  have hi := generatedAxis_localFiber_image (localFiberIncl (cocodeQ h)) r c
  have hm : griessShortPermutation (localFiberIncl (cocodeQ h)).val.2 r = r := by
    change griessShortPermutation 1 r = r
    rw [map_one]
    rfl
  rw [hm, cocodeQ_short_phase, hp, zero_add] at hi
  exact hi

/-- An actual odd cocode fixing an original short axis transports its first triality image
onto its second image, retaining every Griess coordinate. -/
theorem generatedFeasibleContaining_cocode_square_transport (h : SpinIndex)
    (hh : h 11 = 1) (r : GriessShortIndex) (c : ZMod 2)
    (hp : spinDot h (spinTranslation (griessShortQ r)) = 0) :
    rhoLocal (inclQ (cocodeQ h)) (sExtra (conwayShortAxis r c)) =
      sExtra (sExtra (conwayShortAxis r c)) := by
  let a := rhoLocal (inclQ (cocodeQ h))
  have hc : a * sExtra * a⁻¹ = sExtra⁻¹ := cocodeQ_conjugates_sExtra_inverse h hh
  have he : a * sExtra = sExtra⁻¹ * a := by
    calc
      a * sExtra = (a * sExtra * a⁻¹) * a := by group
      _ = sExtra⁻¹ * a := by rw [hc]
  have ht := LinearEquiv.congr_fun he (conwayShortAxis r c)
  change rhoLocal (inclQ (cocodeQ h)) (sExtra (conwayShortAxis r c)) =
    sExtra.symm (rhoLocal (inclQ (cocodeQ h)) (conwayShortAxis r c)) at ht
  rw [generatedFeasibleContaining_cocode_short_fixed h r c hp] at ht
  rw [ht, generatedFeasibleContaining_triality_square_inverse]

/-- The original binary cocode with entries one at positions eleven and zero. -/
def generatedFeasibleContainingCoordinateReflection : SpinIndex := Pi.single 11 1 + Pi.single 0 1

/-- This original binary cocode is odd. -/
theorem generatedFeasibleContainingCoordinateReflection_odd :
    generatedFeasibleContainingCoordinateReflection 11 = 1 := by
  simp [generatedFeasibleContainingCoordinateReflection]

/-- Its phase on original encoder label 2063 and sign index zero vanishes exactly. -/
theorem generatedFeasibleContainingCoordinateReflection_phase :
    spinDot generatedFeasibleContainingCoordinateReflection
      (spinTranslation (griessShortQ generatedFeasibleContainingOctadPrototypeLabel)) = 0 := by
  rw [generatedFeasibleContainingOctadPrototypeLabel, griessOctad_translation,
    generatedFeasibleContainingOctadPrototypeIndex_label]
  have hz : griessOctadOmegaCoefficient 0 = 0 := by decide +kernel
  rw [hz, zero_smul, add_zero]
  change spinDot (Pi.single 11 1 + Pi.single 0 1) (golayLabelCoefficients 2063) = 0
  rw [spinDot_add_left]
  have hd (i : Fin 12) (t : SpinIndex) : spinDot (Pi.single i 1) t = t i := by
    simp [spinDot, Pi.single_apply]
  rw [hd, hd]
  decide +kernel

/-- The second containing prototype lies in the same actual first-axis stabilizer orbit. -/
theorem generatedFeasibleContainingTrialitySquare_mem :
    generatedFeasibleContainingTrialitySquare ∈
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination := by
  let h : localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    ⟨inclQ (cocodeQ generatedFeasibleContainingCoordinateReflection),
      generatedFeasibleContaining_odd_cocode_first_fixed _
        generatedFeasibleContainingCoordinateReflection_odd _⟩
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨h, ?_⟩
  change rhoLocal (inclQ (cocodeQ generatedFeasibleContainingCoordinateReflection))
    (sExtra (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0)) =
      sExtra (sExtra (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0))
  exact generatedFeasibleContaining_cocode_square_transport _
    generatedFeasibleContainingCoordinateReflection_odd _ _
      generatedFeasibleContainingCoordinateReflection_phase

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
