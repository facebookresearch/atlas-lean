/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenClassRootedTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadProjectedLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingCoordinateSourceGeometry

/-! Actual positive root flags for reversing the one-quarter transition. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option autoImplicit false
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

/-- The original odd source has the same positive one-quarter coefficient at the outside root. -/
theorem generatedFeasibleSixteenOddInitial_coefficient :
    (griessConwayEncode generatedOddAxis).2.1
      (Sum.inl (0, generatedFeasibleSixteenOddInitialPair)) = 1 / 4 := by
  rw [generatedOddAxis, generatedAxis_triality_odd_pair_coordinate,
    generatedFeasibleSixteenOddInitialPair_coordinates]
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  simp only [griessShortVector, griessShortIntegral, Fin.val_zero, hm,
    Nat.zero_testBit, Bool.false_eq_true, ite_false, one_mul]
  norm_num
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith

/-- A genuine whole odd-source fixer transports the original incident root to the outside root. -/
theorem generatedFeasibleSixteenOdd_first_root_transport :
    ∃ h : H, rhoLocal h generatedOddAxis = generatedOddAxis ∧
      rhoLocal h (conwayShortAxis (Sum.inl (0, generatedFeasibleOddDestinationPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddInitialPair)) 0 := by
  have hi : griessCoordinatePair generatedFeasibleSixteenOddInitialPair ∈
      generatedFeasibleOddFramePairs := by
    rw [generatedFeasibleSixteenOddInitialPair_coordinates]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩
  obtain ⟨e, _, he, hp⟩ := generatedFeasibleOddFrame_monomial 0
    generatedFeasibleSixteenOddInitialPair hi
  obtain ⟨f, hf, hfix⟩ := generatedOddAxis_projected_stabilizer_lift e he
  have hlabel : griessShortPermutation f.val.2
      (Sum.inl (0, generatedFeasibleSixteenOddInitialPair)) =
        Sum.inl (0, generatedFeasibleOddDestinationPair) := by rw [hf]; exact hp
  have hz := generatedFeasibleSixteen_phase_from_coefficient f generatedOddAxis
    generatedOddAxis _ _ hlabel hfix (1 / 4) (by norm_num)
      generatedFeasibleSixteenOddInitial_coefficient generatedFeasibleOddDestination_first_coordinate
  have hfirst : rhoLocal (localFiberIntoH f)
      (conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddInitialPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleOddDestinationPair)) 0 := by
    change localGriessRepresentation f _ = _
    rw [generatedAxis_localFiber_image, hlabel, hz, zero_add]
  refine ⟨(localFiberIntoH f)⁻¹, ?_, ?_⟩
  · exact generatedFeasibleContaining_inverse_transports _ _ _ hfix
  · exact generatedFeasibleContaining_inverse_transports _ _ _ hfirst

/-- A genuine complete source transport places the existing odd class at the checked outside flag. -/
theorem generatedFeasibleSixteenOdd_source_flag :
    ∃ h : H,
      rhoLocal h generatedFeasibleSecondaryOddDestination = generatedOddAxis ∧
      rhoLocal h (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddInitialPair)) 0 := by
  obtain ⟨a, ha, hax⟩ := generatedFeasibleOddDestination_source_transport
  obtain ⟨b, hbx, hb⟩ := generatedFeasibleSixteenOdd_first_root_transport
  refine ⟨b * a, ?_, ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply, hax, hbx]
  · rw [map_mul, LinearEquiv.mul_apply, ha, hb]

/-- The displayed original Mathieu word sends8−9 to8−10 and preserves the entire octad. -/
def generatedFeasibleSixteenOctadFlagPermutation : golayAutomorphismSubgroup :=
  (omegaOrbitGolayPermutation 0)⁻¹ * (omegaOrbitGolayPermutation 0)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹ * omegaOrbitGolayPermutation 1 *
    omegaOrbitGolayPermutation 0 * omegaOrbitGolayPermutation 0 *
    omegaOrbitGolayPermutation 1 * (omegaOrbitGolayPermutation 0)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹ * omegaOrbitGolayPermutation 1 *
    omegaOrbitGolayPermutation 0 * omegaOrbitGolayPermutation 0 * omegaOrbitGolayPermutation 0

theorem generatedFeasibleSixteenOctadFlagPermutation_first :
    generatedFeasibleSixteenOctadFlagPermutation.val 8 = 8 ∧
      generatedFeasibleSixteenOctadFlagPermutation.val 9 = 10 := by decide +kernel

theorem generatedFeasibleSixteenOctadFlagPermutation_word :
    golayPermute generatedFeasibleSixteenOctadFlagPermutation.val
      (golayOctadWord generatedOctadBasisOctad) =
        golayOctadWord generatedOctadBasisOctad := by
  have ho : golayOctadLabel generatedOctadBasisOctad = 3 :=
    congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
      ⟨3, by decide⟩)
  rw [golayOctadWord, ho]
  decide +kernel

/-- The flag word's full actual spatial action carries the positive incident integral root. -/
theorem generatedFeasibleSixteenOctadFlagPermutation_label :
    griessShortPermutation (golayPermutationIsometry generatedFeasibleSixteenOctadFlagPermutation)
      (Sum.inl (0, generatedFeasibleContainingIncidentPair)) =
        Sum.inl (0, generatedFeasibleSixteenOddFinalPair) := by
  obtain ⟨h8, h9⟩ := generatedFeasibleSixteenOctadFlagPermutation_first
  apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
  left
  apply Subtype.ext
  rw [leechIntegralAction_golayPermutation]
  funext i
  have hi8 : generatedFeasibleSixteenOctadFlagPermutation.val.symm i = 8 ↔ i = 8 := by
    rw [Equiv.symm_apply_eq, h8]
  have hi9 : generatedFeasibleSixteenOctadFlagPermutation.val.symm i = 9 ↔ i = 10 := by
    rw [Equiv.symm_apply_eq, h9]
  simp only [golayIntegerPermute, griessShortLatticeVector, griessShortIntegral,
    generatedFeasibleContainingIncidentPair_coordinates,
    generatedFeasibleSixteenOddFinalPair_coordinates, hi8, hi9, ite_true]

/-- The actual standard-octad coefficient at the final positive root is one. -/
theorem generatedFeasibleSixteenOctadFinal_coefficient :
    (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1
      (Sum.inl (0, generatedFeasibleSixteenOddFinalPair)) = 1 := by
  rw [generatedOctadLocalAxis, generatedAxis_triality_octad_pair_coordinate,
    generatedFeasibleSixteenOddFinalPair_coordinates]
  have hmask : griessOctadSignMask generatedOctadBasisOctad 0 = 0 := by
    simp [griessOctadSignMask, trialityEvenMask, trialityBitWeight8]
  have h8 : (0xff00 : ℕ).testBit 8 = true := by decide
  have h10 : (0xff00 : ℕ).testBit 10 = true := by decide
  simp only [griessShortVector, griessShortIntegral,
    generatedOctadBasisOctad_mask, hmask, Nat.zero_testBit,
    Bool.false_eq_true, ite_false, ite_true]
  norm_num
  rw [h8, h10]
  norm_num
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith

/-- The actual standard-octad coefficient at the original incident root is one. -/
theorem generatedFeasibleSixteenOctadIncident_coefficient :
    (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1
      (Sum.inl (0, generatedFeasibleContainingIncidentPair)) = 1 := by
  rw [generatedOctadLocalAxis, generatedAxis_triality_octad_pair_coordinate,
    generatedFeasibleContainingIncidentPair_coordinates]
  have hmask : griessOctadSignMask generatedOctadBasisOctad 0 = 0 := by
    simp [griessOctadSignMask, trialityEvenMask, trialityBitWeight8]
  have h8 : (0xff00 : ℕ).testBit 8 = true := by decide
  have h9 : (0xff00 : ℕ).testBit 9 = true := by decide
  simp only [griessShortVector, griessShortIntegral,
    generatedOctadBasisOctad_mask, hmask, Nat.zero_testBit,
    Bool.false_eq_true, ite_false, ite_true]
  norm_num
  rw [h8, h9]
  norm_num
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith

/-- A genuine whole-source fixer transports the standard incident octad flag. -/
theorem generatedFeasibleSixteenOctad_first_root_transport :
    ∃ h : H, rhoLocal h (generatedOctadLocalAxis 0 0) = generatedOctadLocalAxis 0 0 ∧
      rhoLocal h (conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddFinalPair)) 0 := by
  let e := golayPermutationIsometry generatedFeasibleSixteenOctadFlagPermutation
  have he : generatedAxisE8ImageSection e (golayOctadWord generatedOctadBasisOctad) =
      generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad) := by
    rw [generatedAxisE8_permutation_image, generatedFeasibleSixteenOctadFlagPermutation_word]
  obtain ⟨f, hf, hfix⟩ := generatedOctad_projected_stabilizer_lift 0 0 e he
  have hp : griessShortPermutation f.val.2
      (Sum.inl (0, generatedFeasibleContainingIncidentPair)) =
        Sum.inl (0, generatedFeasibleSixteenOddFinalPair) := by
    rw [hf]
    exact generatedFeasibleSixteenOctadFlagPermutation_label
  have hz := generatedFeasibleSixteen_phase_from_coefficient f
    (generatedOctadLocalAxis 0 0) (generatedOctadLocalAxis 0 0) _ _ hp hfix 1 (by norm_num)
      generatedFeasibleSixteenOctadIncident_coefficient generatedFeasibleSixteenOctadFinal_coefficient
  refine ⟨localFiberIntoH f, hfix, ?_⟩
  change localGriessRepresentation f _ = _
  rw [generatedAxis_localFiber_image, hp, hz, zero_add]

/-- A complete actual source transport puts the containing source at the final incident flag. -/
theorem generatedFeasibleSixteenOctad_source_flag :
    ∃ h : H, rhoLocal h generatedFeasibleContainingOctadDestination = generatedOctadLocalAxis 0 0 ∧
      rhoLocal h (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddFinalPair)) 0 := by
  obtain ⟨b, hb, hbf⟩ := generatedFeasibleSixteenOctad_first_root_transport
  let a := generatedFeasibleContainingCoordinateSourceWord
  refine ⟨b * a.val, ?_, ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply,
      generatedFeasibleContainingCoordinateSourceWord_axis, hb]
  · rw [map_mul, LinearEquiv.mul_apply,
      generatedFeasibleContainingCoordinateSourceWord_first, hbf]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
