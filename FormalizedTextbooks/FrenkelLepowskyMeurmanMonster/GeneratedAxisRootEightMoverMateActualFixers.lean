/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedActualFixers

/-! Four genuine whole-axis fixer attainments with all original matrix, short and tensor coordinates. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Fixing the entire actual three coordinate summands fixes the actual canonical axis. -/
theorem generatedRootEight_canonical_axis_of_components (f : localFiberSubgroup)
    (hm : localMatrixRepresentation f (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 =
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1)
    (hc : localShortRepresentation f (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 =
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1)
    (ht : localTensorRepresentation f (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 =
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2) :
    rhoLocal (localFiberIntoH f) generatedRootEightCanonicalPositiveAxis =
      generatedRootEightCanonicalPositiveAxis := by
  change localGriessRepresentation f generatedRootEightCanonicalPositiveAxis = _
  have he : griessConwayEncode (localGriessRepresentation f generatedRootEightCanonicalPositiveAxis) =
      griessConwayEncode generatedRootEightCanonicalPositiveAxis := by
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change (localMatrixRepresentation f (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1,
      (localShortRepresentation f (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1,
        localTensorRepresentation f (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2)) = _
    rw [hm, hc, ht]
  have hd := congrArg griessConwayDecode he
  simpa only [griessConwayDecode_encode] using hd

/-- The original corrected mover fixes the whole actual axis, with its genuine central phase retained. -/
theorem generatedRootEight_mover_corrected_canonical_axis :
    rhoLocal generatedRootEightMoverCorrectedLocal generatedRootEightCanonicalPositiveAxis =
      generatedRootEightCanonicalPositiveAxis := by
  apply generatedRootEight_canonical_axis_of_components generatedRootEightMoverCorrectedFiber
    generatedRootEight_mover_corrected_canonical_matrix
    (generatedRootEight_four_actual_short_fixation 2)
  exact funext fun t => funext (generatedRootEight_mover_corrected_canonical_tensor t)

/-- The original corrected mate fixes the whole actual axis, with every original negative orientation retained. -/
theorem generatedRootEight_mate_corrected_canonical_axis :
    rhoLocal generatedRootEightMateCorrectedLocal generatedRootEightCanonicalPositiveAxis =
      generatedRootEightCanonicalPositiveAxis := by
  apply generatedRootEight_canonical_axis_of_components generatedRootEightMateCorrectedFiber
    generatedRootEight_mate_corrected_canonical_matrix
    (generatedRootEight_four_actual_short_fixation 3)
  exact funext fun t => funext (generatedRootEight_mate_corrected_canonical_tensor t)

/-- Every original reduced Mathieu spatial generator has a genuine whole-axis fixer above it. -/
theorem generatedRootEight_mathieu_actual_fixer_projection (j : Fin 2) :
    ∃ h : H,
      projH h = QuotientGroup.mk' signsSubgroup
        (golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j)) ∧
      rhoLocal h generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis := by
  obtain ⟨c, hc⟩ := generatedRootEight_mathieu_reduced_actual_whole_axis_fixer j
  refine ⟨inclQ (qCentral c) * generatedRootEightMathieuReducedCertifiedLocal j, ?_, hc⟩
  rw [map_mul, projH_inclQ, one_mul, generatedRootEight_mathieu_reduced_certified_projection]

/-- The original positive spatial mover is attained by a genuine actual whole-axis fixer. -/
theorem generatedRootEight_mover_actual_fixer_projection :
    ∃ h : H, projH h = QuotientGroup.mk' signsSubgroup leechNormSixHS100PointMover ∧
      rhoLocal h generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis := by
  refine ⟨generatedRootEightMoverCorrectedLocal, ?_, generatedRootEight_mover_corrected_canonical_axis⟩
  change QuotientGroup.mk' signsSubgroup generatedRootEightMoverCorrectedFiber.val.2 = _
  rw [generatedRootEight_mover_tensor_spatial]

/-- The original mate orientation is attained by a genuine actual whole-axis fixer. -/
theorem generatedRootEight_mate_actual_fixer_projection :
    ∃ h : H, projH h = QuotientGroup.mk' signsSubgroup leechNormSixHS100MateOrientation ∧
      rhoLocal h generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis := by
  refine ⟨generatedRootEightMateCorrectedLocal, ?_, generatedRootEight_mate_corrected_canonical_axis⟩
  change QuotientGroup.mk' signsSubgroup generatedRootEightMateCorrectedFiber.val.2 = _
  rw [generatedRootEight_mate_tensor_spatial]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
