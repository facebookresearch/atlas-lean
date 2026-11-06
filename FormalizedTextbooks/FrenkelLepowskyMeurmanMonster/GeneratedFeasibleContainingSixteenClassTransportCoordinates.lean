/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenInputRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadDestination
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOddDestinationOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2XiTransitions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFinitePairIndex

/-! Original physical root addresses for the one-quarter class identification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original outside minus-pair root on coordinates22 and23. -/
def generatedFeasibleSixteenOddInitialPair : Fin 276 := griessPairIndex 22 23 (by decide)
/-- The original middle minus-pair root on coordinates21 and22. -/
def generatedFeasibleSixteenOddMiddlePair : Fin 276 := griessPairIndex 21 22 (by decide)
/-- The original final minus-pair root on coordinates8 and10. -/
def generatedFeasibleSixteenOddFinalPair : Fin 276 := griessPairIndex 8 10 (by decide)

theorem generatedFeasibleSixteenOddInitialPair_coordinates :
    griessCoordinatePair generatedFeasibleSixteenOddInitialPair = (22, 23) := by
  rw [generatedFeasibleSixteenOddInitialPair, griessPairIndex_coordinates]
  rfl

theorem generatedFeasibleSixteenOddMiddlePair_coordinates :
    griessCoordinatePair generatedFeasibleSixteenOddMiddlePair = (21, 22) := by
  rw [generatedFeasibleSixteenOddMiddlePair, griessPairIndex_coordinates]
  rfl

theorem generatedFeasibleSixteenOddFinalPair_coordinates :
    griessCoordinatePair generatedFeasibleSixteenOddFinalPair = (8, 10) := by
  rw [generatedFeasibleSixteenOddFinalPair, griessPairIndex_coordinates]
  rfl

theorem generatedFeasibleSixteenOddMiddle_output_coefficient :
    generatedAxisGlobalOddRoot06OctadSparseShortQ
      (Sum.inl (0, generatedFeasibleSixteenOddMiddlePair)) = 1 := by
  have hp : generatedFeasibleSixteenOddMiddlePair = 273 := by
    rw [generatedFeasibleSixteenOddMiddlePair,
      ← generatedAxisGlobalFinitePairIndex_actual]
    rfl
  rw [hp]
  rfl

/-- Equality of a nonzero actual short coefficient determines the full binary sign. -/
theorem generatedFeasibleSixteen_phase_from_coefficient
    (f : localFiberSubgroup) (x y : GriessSpace) (r s : GriessShortIndex)
    (hp : griessShortPermutation f.val.2 r = s)
    (hxy : localGriessRepresentation f x = y)
    (a : ℝ) (ha : a ≠ 0)
    (hx : (griessConwayEncode x).2.1 r = a)
    (hy : (griessConwayEncode y).2.1 s = a) :
    localShortPhase f r = 0 := by
  have he := congrArg (fun z : GriessSpace => (griessConwayEncode z).2.1 s) hxy
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at he
  change localShortOperator f (griessConwayEncode x).2.1 s = _ at he
  rw [← hp, localShortOperator_image, hx, hp, hy] at he
  have he' : qSign (localShortPhase f r) * a = 1 * a := by simpa only [one_mul] using he
  exact (qSign_eq_one_iff _).mp (mul_right_cancel₀ ha he')

/-- The actual source word carries the positive original outside pair to the positive middle pair. -/
theorem generatedFeasibleSixteenOddRootWord_first :
    rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6)
      (conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddInitialPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddMiddlePair)) 0 := by
  have hi : generatedFeasibleSixteenOddInitialPair = 275 := by
    rw [generatedFeasibleSixteenOddInitialPair, ← generatedAxisGlobalFinitePairIndex_actual]
    rfl
  have hm : generatedFeasibleSixteenOddMiddlePair = 273 := by
    rw [generatedFeasibleSixteenOddMiddlePair, ← generatedAxisGlobalFinitePairIndex_actual]
    rfl
  have hl : generatedAxisGlobalOddShortRootLabels 6 275 = Sum.inl (0, 273) := by
    decide +kernel
  have hc : generatedAxisGlobalOddShortRootPhases 6 275 = 0 := by
    decide +kernel
  have h := generatedAxisGlobalOddShortRoot06Batch01_QImage 19
  change generatedAxisGlobalOddRootQFast 6 (generatedAxisGlobalPairQFinite 0 275) =
    qCentral (generatedAxisGlobalOddShortRootPhases 6 275) *
      generatedAxisGlobalShortQFinite (generatedAxisGlobalOddShortRootLabels 6 275) at h
  rw [hl, hc, generatedAxisGlobalPairQFinite_actual,
    generatedAxisGlobalShortQFinite_actual] at h
  rw [← generatedAxisGlobalOddRootQFast_actual 6 generatedAxisGlobalOddRootQCache06_certificate,
    ← generatedAxisGlobalOddSourceFastRoot_actual, generatedAxisGlobalOddSourceRoot_QImage] at h
  have hb := generatedAxisGlobalOddSourceRoot_short_basis 6 (Sum.inl (0, 275))
    (Sum.inl (0, 273)) 0 h
  have he := congrFun hb
    (griessShortPermutation (generatedAxisGlobalOddSourceRootFiber 6).val.2 (Sum.inl (0, 275)))
  rw [localShortOperator_image] at he
  have hp : griessShortPermutation (generatedAxisGlobalOddSourceRootFiber 6).val.2
      (Sum.inl (0, 275)) = Sum.inl (0, 273) := by
    by_contra hn
    simp only [Pi.single_eq_same, mul_one, qSign_zero, one_smul,
      Pi.single_eq_of_ne hn] at he
    have hs := qSign_sq (localShortPhase (generatedAxisGlobalOddSourceRootFiber 6)
      (Sum.inl (0, 275)))
    nlinarith
  have hz : localShortPhase (generatedAxisGlobalOddSourceRootFiber 6) (Sum.inl (0, 275)) = 0 := by
    apply (qSign_eq_one_iff _).mp
    simpa only [hp, Pi.single_eq_same, mul_one, qSign_zero, one_smul] using he
  rw [hi, hm, ← generatedAxisGlobalOddSourceRootFiber_local]
  change localGriessRepresentation (generatedAxisGlobalOddSourceRootFiber 6) _ = _
  rw [generatedAxis_localFiber_image, hp, hz, zero_add]

/-- The complete original final frame sends the middle root line to the incident target pair. -/
theorem generatedFeasibleSixteenOddFrame_first_label :
    griessShortPermutation generatedAxisGlobalOddRoot06OctadStandardFrameIsometry
      (Sum.inl (0, generatedFeasibleSixteenOddMiddlePair)) =
        Sum.inl (0, generatedFeasibleSixteenOddFinalPair) := by
  have hq : ∀ i : Fin 24,
      generatedAxisGlobalOddRoot06OctadStandardFrameQ i 21 -
        generatedAxisGlobalOddRoot06OctadStandardFrameQ i 22 =
          -(if i = 8 then (1 : ℚ) else 0) + (if i = 10 then 1 else 0) := by
    decide +kernel
  apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
  right
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding, ← leechIsomMatrix_mulVec,
    generatedAxisGlobalOddRoot06OctadStandardFrame_actual]
  have hu : leechCoordinateEmbedding
      (griessShortLatticeVector (Sum.inl (0, generatedFeasibleSixteenOddMiddlePair))).val =
        (4 / Real.sqrt 8 : ℝ) • (Pi.single 21 1 - Pi.single 22 1) := by
    ext i
    by_cases h21 : i = 21 <;> by_cases h22 : i = 22 <;>
      simp [leechCoordinateEmbedding, griessShortLatticeVector, griessShortIntegral,
        generatedFeasibleSixteenOddMiddlePair_coordinates, h21, h22]; ring
  rw [hu, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_single, Matrix.mulVec_single]
  ext i
  have he : (generatedAxisGlobalOddRoot06OctadStandardFrameQ i 21 : ℝ) -
      (generatedAxisGlobalOddRoot06OctadStandardFrameQ i 22 : ℝ) =
        -(if i = 8 then (1 : ℝ) else 0) + (if i = 10 then 1 else 0) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (hq i)
    by_cases h8 : i = 8 <;> by_cases h10 : i = 10 <;>
      simpa [h8, h10] using h
  simp only [op_smul_eq_smul, one_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  change 4 / Real.sqrt 8 *
    ((generatedAxisGlobalOddRoot06OctadStandardFrameQ i 21 : ℝ) -
      (generatedAxisGlobalOddRoot06OctadStandardFrameQ i 22 : ℝ)) =
        leechCoordinateEmbedding
          (-griessShortLatticeVector (Sum.inl (0, generatedFeasibleSixteenOddFinalPair))).val i
  rw [he]
  by_cases h8 : i = 8 <;> by_cases h10 : i = 10 <;>
    simp [leechCoordinateEmbedding, griessShortLatticeVector, griessShortIntegral,
      generatedFeasibleSixteenOddFinalPair_coordinates, h8, h10] <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
