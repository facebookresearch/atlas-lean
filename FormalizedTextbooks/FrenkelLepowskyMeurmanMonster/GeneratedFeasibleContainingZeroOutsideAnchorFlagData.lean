/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryOutsideOctadOrbit

/-! Original Mathieu transport places both actual bridge endpoints at the physical first flag. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exact original encoder labels after the genuine source Mathieu inverse word. -/
def generatedFeasibleContainingZeroOutsideAnchorFlagCode : Fin 2 → Fin 4096 := ![256, 2318]

theorem generatedFeasibleContainingZeroOutsideAnchorFlagCode_mem : ∀ k : Fin 2,
    generatedFeasibleContainingZeroOutsideAnchorFlagCode k ∈ golayOctads := by decide +kernel

/-- Both endpoint octads are bound to the actual preferred dictionary. -/
def generatedFeasibleContainingZeroOutsideAnchorFlagOctad (k : Fin 2) : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨generatedFeasibleContainingZeroOutsideAnchorFlagCode k,
      generatedFeasibleContainingZeroOutsideAnchorFlagCode_mem k⟩

theorem generatedFeasibleContainingZeroOutsideAnchorFlagOctad_label (k : Fin 2) :
    golayOctadLabel (generatedFeasibleContainingZeroOutsideAnchorFlagOctad k) =
      generatedFeasibleContainingZeroOutsideAnchorFlagCode k :=
  congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply _)

/-- The positive preferred labels of both transported endpoint octads. -/
def generatedFeasibleContainingZeroOutsideAnchorFlagLabel (k : Fin 2) : GriessShortIndex :=
  Sum.inr (Sum.inl (generatedFeasibleContainingZeroOutsideAnchorFlagOctad k, 0))

private theorem zero_sign_mask (o : Fin 759) : griessOctadSignMask o 0 = 0 := by
  simp [griessOctadSignMask, trialityEvenMask, trialityBitWeight8]

/-- Every physical coordinate of each original flag label is exactly its positive octad bit. -/
theorem generatedFeasibleContainingZeroOutsideAnchorFlagIntegral (k : Fin 2) (i : Fin 24) :
    griessShortIntegral (generatedFeasibleContainingZeroOutsideAnchorFlagLabel k) i =
      if (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorFlagCode k).val).testBit i.val
        then 2 else 0 := by
  simp only [generatedFeasibleContainingZeroOutsideAnchorFlagLabel, griessShortIntegral,
    generatedFeasibleContainingZeroOutsideAnchorFlagOctad_label, zero_sign_mask,
    Nat.zero_testBit, Bool.false_eq_true, ite_false]

private theorem strong_word_apply (w : List (Fin 28)) (i : Fin 24) :
    (golayStrongWord w).val i = golayStrongWordArray w i := by
  induction w generalizing i with
  | nil => rfl
  | cons t w ih =>
    change (golayStrongLetter t).val ((golayStrongWord w).val i) = _
    rw [golayOutsidePairOctad_strong_letter_apply, ih]
    rfl

private theorem conjugator_apply (i : Fin 24) :
    generatedFeasibleContainingZeroXiConjugator.val i =
      generatedFeasibleContainingZeroXiConjugatorArray i := strong_word_apply [0, 27, 14] i

/-- Both actual whole source octad supports are bound to the original inverse Mathieu word. -/
theorem generatedFeasibleContainingZeroOutsideAnchorFlag_coordinates : ∀ k : Fin 2, ∀ i : Fin 24,
    (if (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode
      (if k = 0 then 10 else 6)).val).testBit
        (generatedFeasibleContainingZeroXiConjugatorArray i).val then (2 : ℤ) else 0) =
      if (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorFlagCode k).val).testBit i.val
        then 2 else 0 := by decide +kernel

/-- The exact original source flag transporter is a genuine Leech monomial isometry. -/
def generatedFeasibleContainingZeroOutsideAnchorFlagIsometry : leechIsomSubgroup :=
  golayPermutationIsometry generatedFeasibleContainingZeroXiConjugator⁻¹

private theorem conjugator_inverse_val_symm (i : Fin 24) :
    (generatedFeasibleContainingZeroXiConjugator⁻¹).val.symm i =
      generatedFeasibleContainingZeroXiConjugator.val i := by
  rw [InvMemClass.coe_inv, Equiv.Perm.inv_def, Equiv.symm_symm]

private theorem flag_isometry_apply (u : leechIntegral) (i : Fin 24) :
    (leechIntegralAction generatedFeasibleContainingZeroOutsideAnchorFlagIsometry u).val i =
      u.val (generatedFeasibleContainingZeroXiConjugatorArray i) := by
  rw [generatedFeasibleContainingZeroOutsideAnchorFlagIsometry,
    leechIntegralAction_golayPermutation]
  change u.val ((generatedFeasibleContainingZeroXiConjugator⁻¹).val.symm i) = _
  rw [conjugator_inverse_val_symm, conjugator_apply]

/-- The flag transporter is the Golay monomial with trivial sign and the inverse word. -/
theorem generatedFeasibleContainingZeroOutsideAnchorFlagIsometry_monomial :
    generatedFeasibleContainingZeroOutsideAnchorFlagIsometry ∈ golayMonomialSubgroup := by
  refine ⟨0, generatedFeasibleContainingZeroXiConjugator⁻¹, ?_⟩
  have h0 : golaySignIsometry 0 = 1 := golaySignHom.map_one
  rw [h0, one_mul]
  rfl

/-- Both positive actual preferred octads are transported by the original Mathieu word. -/
theorem generatedFeasibleContainingZeroOutsideAnchorFlagIsometry_octad (k : Fin 2) :
    griessShortPermutation generatedFeasibleContainingZeroOutsideAnchorFlagIsometry
      (Sum.inr (Sum.inl (generatedFeasibleContainingZeroOutsideAnchorOctad
        (if k = 0 then 10 else 6), 0))) =
          generatedFeasibleContainingZeroOutsideAnchorFlagLabel k := by
  apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
  left
  apply Subtype.ext
  funext i
  rw [flag_isometry_apply]
  change griessShortIntegral (Sum.inr (Sum.inl
    (generatedFeasibleContainingZeroOutsideAnchorOctad (if k = 0 then 10 else 6), 0)))
      (generatedFeasibleContainingZeroXiConjugatorArray i) =
    griessShortIntegral (generatedFeasibleContainingZeroOutsideAnchorFlagLabel k) i
  rw [generatedFeasibleContainingZeroOutsideAnchorFlagIntegral]
  simp only [griessShortIntegral, generatedFeasibleContainingZeroOutsideAnchorOctad_label,
    zero_sign_mask, Nat.zero_testBit, Bool.false_eq_true, ite_false]
  exact generatedFeasibleContainingZeroOutsideAnchorFlag_coordinates k i

/-- The actual preferred first pair1−2 is transported to the original positive pair0−1. -/
theorem generatedFeasibleContainingZeroOutsideAnchorFlagIsometry_first :
    griessShortPermutation generatedFeasibleContainingZeroOutsideAnchorFlagIsometry
      (Sum.inl (0, (23 : Fin 276))) =
        Sum.inl (0, generatedFeasiblePhysicalRootPair) := by
  apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
  left
  apply Subtype.ext
  funext i
  rw [flag_isometry_apply]
  have hp0 : generatedFeasibleContainingZeroXiConjugator.val 0 = 1 := by
    rw [conjugator_apply]
    exact generatedFeasibleContainingZeroXiConjugatorArray_flags.1
  have hp1 : generatedFeasibleContainingZeroXiConjugator.val 1 = 2 := by
    rw [conjugator_apply]
    exact generatedFeasibleContainingZeroXiConjugatorArray_flags.2.1
  have hi0 : generatedFeasibleContainingZeroXiConjugatorArray i = 1 ↔ i = 0 := by
    rw [← conjugator_apply, ← hp0]
    exact generatedFeasibleContainingZeroXiConjugator.val.injective.eq_iff
  have hi1 : generatedFeasibleContainingZeroXiConjugatorArray i = 2 ↔ i = 1 := by
    rw [← conjugator_apply, ← hp1]
    exact generatedFeasibleContainingZeroXiConjugator.val.injective.eq_iff
  have hpair : griessCoordinatePair (23 : Fin 276) = (1, 2) := by
    rw [← generatedAxisGlobalPairCoordinates_actual]
    decide +kernel
  change griessShortIntegral (Sum.inl (0, (23 : Fin 276)))
      (generatedFeasibleContainingZeroXiConjugatorArray i) =
    griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) i
  simp only [griessShortIntegral, hpair,
    generatedFeasiblePhysicalRootPair_coordinates, hi0, hi1, ite_true]

/-- The transported source is a member of the entire original outside physical sector. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOutside_mem :
    generatedFeasibleContainingZeroOutsideAnchorFlagLabel 0 ∈ generatedFeasibleSecondaryNonPairLabels 1 := by
  have ho : generatedFeasibleContainingZeroOutsideAnchorFlagOctad 0 ∈
      generatedFeasibleOctadOutsideLabels := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [generatedFeasibleContainingZeroOutsideAnchorFlagOctad_label]
    decide +kernel
  change _ ∈ (generatedFeasibleSecondaryOctadSubset generatedFeasibleOctadOutsideLabels).map _
  refine Finset.mem_map.mpr ⟨(generatedFeasibleContainingZeroOutsideAnchorFlagOctad 0, 0), ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho, ?_⟩
  change griessShortIntegral (generatedFeasibleContainingZeroOutsideAnchorFlagLabel 0) 0 =
    griessShortIntegral (generatedFeasibleContainingZeroOutsideAnchorFlagLabel 0) 1
  rw [generatedFeasibleContainingZeroOutsideAnchorFlagIntegral,
    generatedFeasibleContainingZeroOutsideAnchorFlagIntegral]
  decide +kernel

/-- The transported target is a member of the entire original containing physical sector. -/
theorem generatedFeasibleContainingZeroOutsideAnchorContaining_mem :
    generatedFeasibleContainingZeroOutsideAnchorFlagLabel 1 ∈ generatedFeasibleSecondaryNonPairLabels 0 := by
  have ho : generatedFeasibleContainingZeroOutsideAnchorFlagOctad 1 ∈
      generatedFeasibleOctadContainingLabels := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [generatedFeasibleContainingZeroOutsideAnchorFlagOctad_label]
    decide +kernel
  change _ ∈ (generatedFeasibleSecondaryOctadSubset generatedFeasibleOctadContainingLabels).map _
  refine Finset.mem_map.mpr ⟨(generatedFeasibleContainingZeroOutsideAnchorFlagOctad 1, 0), ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho, ?_⟩
  change griessShortIntegral (generatedFeasibleContainingZeroOutsideAnchorFlagLabel 1) 0 =
    griessShortIntegral (generatedFeasibleContainingZeroOutsideAnchorFlagLabel 1) 1
  rw [generatedFeasibleContainingZeroOutsideAnchorFlagIntegral,
    generatedFeasibleContainingZeroOutsideAnchorFlagIntegral]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
