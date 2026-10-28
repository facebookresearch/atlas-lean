/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroShortCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechQuadratic

/-! An actual whole-source extraspecial element flips both signed external pair phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

private theorem square_sum_add (u v : leechIntegral) :
    leechSquareSum (u + v).val = leechSquareSum u.val + leechSquareSum v.val +
      2 * leechIntegralPairing u.val v.val := by
  unfold leechSquareSum leechIntegralPairing
  simp only [Submodule.coe_add, Pi.add_apply]
  simp_rw [show ∀ a b : ℤ, (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) by
    intro a b; ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The genuine extraspecial phase equals the half-norm of the sum of actual short roots. -/
theorem generatedFeasibleContainingZero_short_phase_half_norm (r s : GriessShortIndex) :
    toAdd (localAxisQPhase r (griessShortQ s)) =
      ((leechSquareSum
        (griessShortLatticeVector r + griessShortLatticeVector s).val / 16 : ℤ) : ZMod 2) := by
  have h := leechHyperbolicCoordinates_halfNorm
    (griessShortLatticeVector r + griessShortLatticeVector s)
  rw [map_add, map_add] at h
  change _ = qBeta (toAdd (griessShortQ r).base + toAdd (griessShortQ s).base)
    (toAdd (griessShortQ r).base + toAdd (griessShortQ s).base) at h
  rw [qBeta_add_left, qBeta_add_right, qBeta_add_right] at h
  have hr := griessShortQ_squareQuad r
  have hs := griessShortQ_squareQuad s
  change qBeta (toAdd (griessShortQ r).base) (toAdd (griessShortQ r).base) = 0 at hr
  change qBeta (toAdd (griessShortQ s).base) (toAdd (griessShortQ s).base) = 0 at hs
  rw [hr, hs, zero_add, add_zero] at h
  change qBeta (toAdd (griessShortQ s).base) (toAdd (griessShortQ r).base) +
    qBeta (toAdd (griessShortQ r).base) (toAdd (griessShortQ s).base) = _
  simpa only [add_comm] using h.symm

/-- Actual orthogonal short roots have zero extraspecial conjugation phase. -/
theorem generatedFeasibleContainingZero_short_phase_orthogonal (r s : GriessShortIndex)
    (h : leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) = 0) :
    localShortPhase (localFiberIncl (griessShortQ s)) r = 0 := by
  rw [localAxisQPhase_eq_short_phase,
    generatedFeasibleContainingZero_short_phase_half_norm, square_sum_add]
  change (((leechSquareSum (griessShortIntegral r) + leechSquareSum (griessShortIntegral s) +
    2 * leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s)) / 16 : ℤ) : ZMod 2) = 0
  rw [griessShortIntegral_squareSum, griessShortIntegral_squareSum, h]
  decide

/-- The original disjoint octad 57 supplies a genuine whole-source phase flip. -/
def generatedFeasibleContainingZeroPhaseLabel : GriessShortIndex :=
  generatedFeasibleContainingZeroCachedIndex (Sum.inr (4, 0))

/-- The preferred original external pair used as the zero-input anchor. -/
def generatedFeasibleContainingZeroShortLabel : GriessShortIndex :=
  generatedFeasibleContainingZeroCachedIndex (Sum.inl (0, 0))

private theorem phase_source_support (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedFeasibleContainingOctadPrototypeIndex r) :
    localShortPhase (localFiberIncl (griessShortQ generatedFeasibleContainingZeroPhaseLabel)) r = 0 := by
  apply generatedFeasibleContainingZero_short_phase_orthogonal
  have hm := (generatedAxisE8ShortLines_coordinate_mem
    generatedFeasibleContainingOctadPrototypeIndex r).mpr hr
  have hzero : generatedFeasibleContainingSelectedShortSquare
      generatedFeasibleContainingZeroPhaseLabel = 0 := by
    have h := generatedFeasibleContainingZeroCachedIndex_mem (Sum.inr (4, 0))
    exact (Finset.mem_filter.mp h).2
  have h := generatedFeasibleContaining_selected_zero_section_orthogonal
    generatedFeasibleContainingZeroPhaseLabel hzero (griessShortLatticeVector r) hm
  change (∑ i : Fin 24, griessShortIntegral generatedFeasibleContainingZeroPhaseLabel i *
    griessShortIntegral r i) = 0 at h
  unfold leechIntegralPairing
  simpa only [mul_comm] using h

/-- The phase flip fixes every actual source coordinate, including the full short component. -/
theorem generatedFeasibleContainingZeroPhase_whole_source :
    rhoLocal (inclQ (griessShortQ generatedFeasibleContainingZeroPhaseLabel))
      generatedFeasibleContainingOctadDestination = generatedFeasibleContainingOctadDestination := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode (localGriessRepresentation
    (localFiberIncl (griessShortQ generatedFeasibleContainingZeroPhaseLabel)) _) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  apply Prod.ext
  · change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  · apply Prod.ext
    · ext r
      have hd := localShortOperator_image
        (localFiberIncl (griessShortQ generatedFeasibleContainingZeroPhaseLabel))
        (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 r
      change localShortOperator _ _ (griessShortPermutation 1 r) = _ at hd
      rw [map_one, Equiv.Perm.one_apply] at hd
      change localShortOperator _ _ r = _
      rw [hd]
      by_cases hr : generatedOctadShortSupport generatedFeasibleContainingOctadPrototypeIndex r
      · rw [phase_source_support r hr, qSign_zero, one_mul]
      · have hz := not_ne_iff.mp (mt (generatedAxis_triality_octad_support_iff
          generatedFeasibleContainingOctadPrototypeIndex 0 0 r).mp hr)
        change (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 r = 0 at hz
        rw [hz, mul_zero]
    · change localTensorRepresentation
        (localFiberIncl (griessShortQ generatedFeasibleContainingZeroPhaseLabel))
        (griessConwayEncode (sExtra (conwayShortAxis
          (Sum.inr (Sum.inl (generatedFeasibleContainingOctadPrototypeIndex, 0))) 0))).2.2 =
          (griessConwayEncode (sExtra (conwayShortAxis
            (Sum.inr (Sum.inl (generatedFeasibleContainingOctadPrototypeIndex, 0))) 0))).2.2
      rw [generatedAxis_triality_octad_tensor_zero_all, map_zero]

/-- The actual phase correction fixes the original positive first axis. -/
theorem generatedFeasibleContainingZeroPhase_first :
    rhoLocal (inclQ (griessShortQ generatedFeasibleContainingZeroPhaseLabel))
      (conwayAxis generatedFeasiblePhysicalRootPair) = conwayAxis generatedFeasiblePhysicalRootPair := by
  change localFiberIntoH (localFiberIncl (griessShortQ generatedFeasibleContainingZeroPhaseLabel)) ∈
    localAxisStabilizer generatedFeasiblePhysicalRootPair
  rw [localAxisStabilizer_mk_iff]
  constructor
  · change griessShortPermutation 1 _ = _
    rw [map_one]
    rfl
  · have hp : generatedOctadShortSupport generatedFeasibleContainingOctadPrototypeIndex
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
      change generatedOctadPairSupport generatedFeasibleContainingOctadPrototypeIndex
        generatedFeasiblePhysicalRootPair
      unfold generatedOctadPairSupport
      rw [generatedFeasibleContainingOctadPrototypeIndex_label,
        generatedFeasiblePhysicalRootPair_coordinates]
      decide +kernel
    have h := phase_source_support (Sum.inl (0, generatedFeasiblePhysicalRootPair)) hp
    exact h

/-- The genuine phase flip lies in the entire actual first-axis stabilizer. -/
def generatedFeasibleContainingZeroPhaseWord : localAxisStabilizer generatedFeasiblePhysicalRootPair :=
  ⟨inclQ (griessShortQ generatedFeasibleContainingZeroPhaseLabel), generatedFeasibleContainingZeroPhase_first⟩

/-- This actual first-axis word fixes the entire containing source. -/
theorem generatedFeasibleContainingZeroPhaseWord_source :
    rhoLocal generatedFeasibleContainingZeroPhaseWord.val generatedFeasibleContainingOctadDestination =
      generatedFeasibleContainingOctadDestination := generatedFeasibleContainingZeroPhase_whole_source

/-- Both actual signed external-pair phases are interchanged by this whole-source fixer. -/
theorem generatedFeasibleContainingZeroPhaseWord_anchor (c : ZMod 2) :
    rhoLocal generatedFeasibleContainingZeroPhaseWord.val
      (conwayShortAxis generatedFeasibleContainingZeroShortLabel c) =
        conwayShortAxis generatedFeasibleContainingZeroShortLabel (1 + c) := by
  have h := generatedAxis_localFiber_image
    (localFiberIncl (griessShortQ generatedFeasibleContainingZeroPhaseLabel))
      generatedFeasibleContainingZeroShortLabel c
  have hp : griessShortPermutation
      (localFiberIncl (griessShortQ generatedFeasibleContainingZeroPhaseLabel)).val.2
        generatedFeasibleContainingZeroShortLabel = generatedFeasibleContainingZeroShortLabel := by
    change griessShortPermutation 1 _ = _
    rw [map_one]
    rfl
  rw [hp, localAxisQPhase_eq_short_phase,
    generatedFeasibleContainingZero_short_phase_half_norm] at h
  have hn : leechSquareSum
      (griessShortLatticeVector generatedFeasibleContainingZeroShortLabel +
        griessShortLatticeVector generatedFeasibleContainingZeroPhaseLabel).val = 80 := by
    change leechSquareSum
      (fun i => griessShortIntegral generatedFeasibleContainingZeroShortLabel i +
        griessShortIntegral generatedFeasibleContainingZeroPhaseLabel i) = 80
    rw [generatedFeasibleContainingZeroShortLabel, generatedFeasibleContainingZeroPhaseLabel,
      ← generatedFeasibleContainingZeroCachedIntegral_actual,
      ← generatedFeasibleContainingZeroCachedIntegral_actual]
    decide +kernel
  rw [hn, show ((80 / 16 : ℤ) : ZMod 2) = 1 by decide] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
