/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorFixationOfCircuit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortSupportActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateShortSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTensor

/-! A single complete genuine candidate fixes the entire actual axis from its full source certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Whole unchanged source certificates give genuine fixation of one entire actual axis. -/
theorem generatedTwelfth_candidate_axis_fix_of_complete_certificates (g : Fin 12)
    (hshort : ∀ a, generatedTwelfthCompleteShortInputInteger
      (generatedNinthLowerSpinShortIndex a) ≠ 0 → generatedTwelfthCompleteShortCondition g a)
    (hcircuit : ∀ j : Fin 24,
      (generatedTwelfthSpinCompact g).val
        (nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorSpatialInteger g n j)) =
          (generatedTwelfthSpinTensorSpatialDenominator g : ℝ) •
            nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorInputInteger n j)) :
    rhoLocal (generatedTwelfthCertifiedLocal g) generatedTwelfthIncomingCandidateAxis =
      generatedTwelfthIncomingCandidateAxis := by
  have hC : (griessConwayEncode (rhoLocal (generatedTwelfthCertifiedLocal g)
      generatedTwelfthIncomingCandidateAxis)).2.1 =
        (griessConwayEncode generatedTwelfthIncomingCandidateAxis).2.1 := by
    rw [generatedTwelfthCertifiedLocal, generatedFourth_local_short]
    exact generatedTwelfth_complete_short_fix_of_support_cache g hshort _
      generatedTwelfth_candidate_short_source_actual
  have hT : (griessConwayEncode (rhoLocal (generatedTwelfthCertifiedLocal g)
      generatedTwelfthIncomingCandidateAxis)).2.2 =
        (griessConwayEncode generatedTwelfthIncomingCandidateAxis).2.2 := by
    rw [generatedTwelfthCertifiedLocal, generatedFourth_local_tensor,
      generatedTwelfth_candidate_final_tensor_source, map_smul]
    apply congrArg (fun T => (1 / (64 * Real.sqrt 2) : ℝ) • T)
    funext t i
    exact generatedTwelfth_certified_tensor_integer_fix_of_circuit g hcircuit t i
  have he : griessConwayEncode (rhoLocal (generatedTwelfthCertifiedLocal g)
      generatedTwelfthIncomingCandidateAxis) =
        griessConwayEncode generatedTwelfthIncomingCandidateAxis :=
    Prod.ext (generatedTwelfth_certified_candidate_matrix_fix g) (Prod.ext hC hT)
  have hd := congrArg griessConwayDecode he
  simpa only [griessConwayDecode_encode] using hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
