/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMatrixFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhEvenPauliLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhElevenFrameProjection

/-! Entire-axis and exact-order consequences of the two genuine coordinate return gates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The canonical sign choice retains the entire original seventh matrix. -/
theorem generatedSeventhXiPlaneCanonicalMatrix_actual :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).1 =
      generatedSeventhAxisMatrix := by
  obtain ⟨q, _, hq⟩ := generatedSeventhXi_canonical_axis_correction
  have h := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hq
  rw [generatedSeventh_axis_matrix, generatedSeventh_Q_matrix] at h
  exact h.symm

/-- Complete original short and tensor returns imply fixation of the entire canonical axis. -/
theorem generatedSeventhXiPlaneCanonical_fixed_of_returns
    (hX : localShortOperator generatedSeventhXiPlaneFiber
      (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1 =
        (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1)
    (hT : localTensorRepresentation generatedSeventhXiPlaneFiber
      (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2 =
        (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2) :
    rhoLocal (localFiberIntoH generatedSeventhXiPlaneFiber)
      generatedSeventhXiPlaneCanonicalAxis = generatedSeventhXiPlaneCanonicalAxis := by
  have hm : conwayMatrixAction generatedSeventhXiPlaneFiber.val.2
      (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).1 =
        (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).1 := by
    rw [generatedSeventhXiPlaneCanonicalMatrix_actual]
    exact generatedSeventhXiPlane_matrix_fixed
  have he : griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhXiPlaneFiber)
        generatedSeventhXiPlaneCanonicalAxis) =
        griessConwayEncode generatedSeventhXiPlaneCanonicalAxis := by
    apply Prod.ext
    · rw [generatedFourth_local_matrix]
      exact hm
    · apply Prod.ext
      · rw [generatedFourth_local_short]
        exact hX
      · rw [generatedFourth_local_tensor]
        exact hT
  have h := congrArg griessConwayDecode he
  simpa only [griessConwayDecode_encode] using h

/-- The genuine full coordinate returns supply the actual moving-Xi projection. -/
theorem generatedSeventhXiPlane_projected_of_returns
    (hX : localShortOperator generatedSeventhXiPlaneFiber
      (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1 =
        (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1)
    (hT : localTensorRepresentation generatedSeventhXiPlaneFiber
      (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2 =
        (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2) :
    QuotientGroup.mk' signsSubgroup generatedSeventhXiPlaneFiber.val.2 ∈
      generatedSeventhProjectedAxisStabilizer :=
  generatedSeventhXi_canonical_fixer_projected _
    (generatedSeventhXiPlaneCanonical_fixed_of_returns hX hT)

/-- Complete source-coordinate returns yield the exact original local stabilizer cardinality. -/
theorem generatedSeventh_local_stabilizer_card_of_returns
    (hX : localShortOperator generatedSeventhXiPlaneFiber
      (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1 =
        (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1)
    (hT : localTensorRepresentation generatedSeventhXiPlaneFiber
      (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2 =
        (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2) :
    Nat.card generatedSeventhLocalAxisStabilizer = 318504960 :=
  generatedSeventh_local_stabilizer_card_of_xi
    (generatedSeventhXiPlane_projected_of_returns hX hT)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
