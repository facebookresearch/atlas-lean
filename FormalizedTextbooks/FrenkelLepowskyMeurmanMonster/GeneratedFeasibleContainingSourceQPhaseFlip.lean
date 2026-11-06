/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingE7ProjectionTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCocode

/-! A genuine whole-source extraspecial fixer flips the actual normalized signed short anchor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Original encoder label2306 is an actual Golay octad. -/
theorem generatedFeasibleContainingNormalizedOctad_mem : (2306 : Fin 4096) ∈ golayOctads := by
  decide +kernel

/-- The normalized actual source octad is addressed through the entire original dictionary. -/
def generatedFeasibleContainingNormalizedOctadIndex : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨2306, generatedFeasibleContainingNormalizedOctad_mem⟩

/-- The actual normalized dictionary index retains its exact original encoder label. -/
theorem generatedFeasibleContainingNormalizedOctadIndex_label :
    golayOctadLabel generatedFeasibleContainingNormalizedOctadIndex = 2306 :=
  congrArg Subtype.val
    ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
      ⟨2306, generatedFeasibleContainingNormalizedOctad_mem⟩)

/-- The actual preferred all-positive octad short vector at original label2306. -/
def generatedFeasibleContainingNormalizedShortLabel : GriessShortIndex :=
  Sum.inr (Sum.inl (generatedFeasibleContainingNormalizedOctadIndex, 0))

/-- An original even cocode with its actual eighth source coefficient one. -/
def generatedFeasibleContainingSourcePhaseCocode : SpinIndex := Pi.single 8 1

private theorem phase_even : generatedFeasibleContainingSourcePhaseCocode 11 = 0 := by
  simp [generatedFeasibleContainingSourcePhaseCocode]

private theorem phase_source :
    spinDot generatedFeasibleContainingSourcePhaseCocode
      (spinTranslation (griessShortQ generatedFeasibleContainingOctadPrototypeLabel)) = 0 := by
  rw [generatedFeasibleContainingOctadPrototypeLabel, griessOctad_translation,
    generatedFeasibleContainingOctadPrototypeIndex_label]
  have hzero : griessOctadOmegaCoefficient 0 = 0 := by decide +kernel
  rw [hzero, zero_smul, add_zero]
  change spinDot (Pi.single 8 1) (golayLabelCoefficients 2063) = 0
  decide +kernel

/-- The original genuine even cocode has nonzero actual short phase on label2306. -/
theorem generatedFeasibleContainingSourcePhaseCocode_anchor_phase :
    spinDot generatedFeasibleContainingSourcePhaseCocode
      (spinTranslation (griessShortQ generatedFeasibleContainingNormalizedShortLabel)) = 1 := by
  rw [generatedFeasibleContainingNormalizedShortLabel, griessOctad_translation,
    generatedFeasibleContainingNormalizedOctadIndex_label]
  have hzero : griessOctadOmegaCoefficient 0 = 0 := by decide +kernel
  rw [hzero, zero_smul, add_zero]
  change spinDot (Pi.single 8 1) (golayLabelCoefficients 2306) = 1
  decide +kernel

/-- The original even cocode fixes the entire source vector by actual triality commutation.
-/
theorem generatedFeasibleContainingSourcePhaseCocode_whole_source :
    rhoLocal (inclQ (cocodeQ generatedFeasibleContainingSourcePhaseCocode))
      generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingOctadDestination := by
  have hc := monsterNortonEvenCocode_commute_extra
    generatedFeasibleContainingSourcePhaseCocode phase_even
  have h := LinearEquiv.congr_fun hc.eq
    (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0)
  change rhoLocal (inclQ (cocodeQ generatedFeasibleContainingSourcePhaseCocode))
    (sExtra (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0)) =
      sExtra (rhoLocal (inclQ (cocodeQ generatedFeasibleContainingSourcePhaseCocode))
        (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0)) at h
  rw [generatedFeasibleContaining_cocode_short_fixed _ _ _ phase_source] at h
  exact h

/-- The same entire source fixer fixes the actual positive first axis. -/
theorem generatedFeasibleContainingSourcePhaseCocode_first :
    rhoLocal (inclQ (cocodeQ generatedFeasibleContainingSourcePhaseCocode))
      (conwayAxis generatedFeasiblePhysicalRootPair) =
        conwayAxis generatedFeasiblePhysicalRootPair := by
  rw [← conwayShortAxis_pair_zero]
  apply generatedFeasibleContaining_cocode_short_fixed
  rw [griessPairQ_translation]
  simp [spinDot]

/-- The genuine whole-source phase flip as an element of the entire actual first-axis group. -/
def generatedFeasibleContainingSourcePhaseWord :
    localAxisStabilizer generatedFeasiblePhysicalRootPair :=
  ⟨inclQ (cocodeQ generatedFeasibleContainingSourcePhaseCocode),
    generatedFeasibleContainingSourcePhaseCocode_first⟩

/-- The actual first-axis word fixes every coordinate of the original containing source. -/
theorem generatedFeasibleContainingSourcePhaseWord_source :
    rhoLocal generatedFeasibleContainingSourcePhaseWord.val
      generatedFeasibleContainingOctadDestination = generatedFeasibleContainingOctadDestination :=
  generatedFeasibleContainingSourcePhaseCocode_whole_source

/-- The same actual source point stabilizer word flips either genuine binary axis sign of
its entire original normalized short anchor. -/
theorem generatedFeasibleContainingSourcePhaseWord_anchor (c : ZMod 2) :
    rhoLocal generatedFeasibleContainingSourcePhaseWord.val
      (conwayShortAxis generatedFeasibleContainingNormalizedShortLabel c) =
        conwayShortAxis generatedFeasibleContainingNormalizedShortLabel (1 + c) := by
  have h := generatedAxis_localFiber_image
    (localFiberIncl (cocodeQ generatedFeasibleContainingSourcePhaseCocode))
      generatedFeasibleContainingNormalizedShortLabel c
  have hp : griessShortPermutation
      (localFiberIncl (cocodeQ generatedFeasibleContainingSourcePhaseCocode)).val.2
        generatedFeasibleContainingNormalizedShortLabel =
          generatedFeasibleContainingNormalizedShortLabel := by
    change griessShortPermutation 1 _ = _
    rw [map_one]
    rfl
  rw [hp, cocodeQ_short_phase, generatedFeasibleContainingSourcePhaseCocode_anchor_phase] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
