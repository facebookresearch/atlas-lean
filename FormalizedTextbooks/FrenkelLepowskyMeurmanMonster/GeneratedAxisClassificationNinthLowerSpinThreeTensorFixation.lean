/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeTensorCircuit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorFixationGeneric

/-! Actual tensor fixation follows from the complete circuit and two explicit source bindings:
all input coordinates, and the genuine rational spatial action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every literal spatial denominator is positive. -/
theorem generatedNinth_lower_spin_three_tensor_spatial_denominator_positive : ∀ i : Fin 11,
    0 < generatedNinthLowerSpinTensorSpatialDenominator i := by
  exact generatedNinth_lower_spin_tensor_generic_spatial_denominator_positive

/-- Two full source equalities turn the exact compact circuit into genuine local tensor fixation.
The input equality covers every actual spin coordinate and all 24 physical columns. -/
theorem generatedNinth_lower_spin_three_tensor_fix_of_source_caches (g : Fin 3)
    (T : SpinIndex → Fin 24 → ℝ)
    (hinput : ∀ t j, 64 * Real.sqrt 2 * T t j =
      (generatedNinthLowerSpinTensorInputInteger (nortonUIntegerLabel t) j : ℝ))
    (hspatial : ∀ j k, (generatedNinthLowerSpinTensorSpatialDenominator
      (generatedNinthLowerSpinThreeCandidateIndex g) : ℝ) *
      (generatedNinthLowerSpinDirectIsometry (generatedNinthLowerSpinThreeCandidateIndex
        g)).val (Pi.single k 1) j =
        (generatedNinthLowerSpinTensorSpatialNumerator
          (generatedNinthLowerSpinThreeCandidateIndex g) j k : ℝ)) :
    localTensorRepresentation (generatedNinthLowerSpinDirectFiber
      (generatedNinthLowerSpinThreeCandidateIndex g)) T = T := by
  exact generatedNinth_lower_spin_tensor_fix_of_circuit_and_source_caches
    (generatedNinthLowerSpinThreeCandidateIndex g) T hinput hspatial
    (generatedNinth_lower_spin_three_tensor_circuit g)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
