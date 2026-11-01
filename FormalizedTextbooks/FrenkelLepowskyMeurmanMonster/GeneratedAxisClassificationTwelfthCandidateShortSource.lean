/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateTensor

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateShortFormulaActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateShortSourceCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingShortCertificates

/-! Every actual candidate short coordinate is bound to its exact complete integer cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- The entire actual candidate short constituent has the complete exact original source cache. -/
theorem generatedTwelfth_candidate_short_source_actual (r : GriessShortIndex) :
    128 * (griessConwayEncode generatedTwelfthIncomingCandidateAxis).2.1 r =
      (generatedTwelfthCompleteShortInputInteger r : ℝ) := by
  have ht (t : SpinIndex) (i : Fin 24) :
      (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
        generatedFifthAxis)).2.2 t i =
        (generatedTwelfthIncomingSpinTensorOutputInteger (nortonUIntegerLabel t) i : ℝ) /
          (64 * Real.sqrt 2) := by
    apply (eq_div_iff (by positivity : (64 : ℝ) * Real.sqrt 2 ≠ 0)).mpr
    simpa only [mul_comm] using generatedTwelfth_incoming_candidate_tensor_actual t i
  rw [generatedTwelfth_candidate_short_formula_generic_actual
    generatedTwelfth_incoming_short_actual ht, generatedTwelfth_candidate_short_source_formula]
  norm_cast

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
