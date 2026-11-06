/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorCircuit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorInputSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorMatrixReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTensor

/-! Complete genuine incoming tensor coefficients from the canonical source and certified replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

private theorem numerator_binding :
    generatedTwelfthIncomingSpinTensorSpatialNumerator 0 =
      generatedTwelfthIncomingCertifiedNumerator := by
  ext i j
  have h : ∀ i j : Fin 24, generatedTwelfthIncomingSpinTensorSpatialNumerator 0 i j =
      generatedTwelfthIncomingCertifiedNumerator i j := by
    decide +kernel
  exact h i j

/-- The complete candidate action on the integer source has precisely the displayed output packet. -/
theorem generatedTwelfth_incoming_candidate_tensor_integer (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation generatedTwelfthIncomingCertifiedFiber
      (fun u j => (generatedTwelfthIncomingSpinTensorInputInteger (nortonUIntegerLabel u) j : ℝ))
        t i =
      (generatedTwelfthIncomingSpinTensorOutputInteger (nortonUIntegerLabel t) i : ℝ) / 4 := by
  apply generatedTwelfth_tensor_matrix_column_replay generatedTwelfthIncomingCertifiedFiber
    generatedTwelfthIncomingCertifiedNumerator 4 (by decide)
  · change (4 : ℝ) • leechIsomMatrix generatedTwelfthIncomingCertifiedSpatial = _
    exact generatedTwelfth_certified_isometry_numerator
      generatedTwelfthIncomingCertifiedNumerator generatedTwelfthIncomingCertifiedIntegral
      generatedTwelfthIncomingCertifiedIntegralInverse 4 (by decide)
      generatedTwelfth_incoming_certified_orthogonal_left
      generatedTwelfth_incoming_certified_orthogonal_right
      generatedTwelfth_incoming_certified_basis
      generatedTwelfth_incoming_certified_integral_inverse
  · intro j
    dsimp only [generatedTwelfthIncomingCertifiedFiber]
    rw [← numerator_binding]
    exact generatedTwelfth_incoming_spin_tensor_circuit 0 j

/-- The full incoming tensor equals its exact output divided by sixty-four square root two. -/
theorem generatedTwelfth_incoming_candidate_tensor_actual (t : SpinIndex) (i : Fin 24) :
    64 * Real.sqrt 2 *
      (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
        generatedFifthAxis)).2.2 t i =
      (generatedTwelfthIncomingSpinTensorOutputInteger (nortonUIntegerLabel t) i : ℝ) := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hsource : (griessConwayEncode generatedFifthAxis).2.2 =
      (1 / (16 * Real.sqrt 2) : ℝ) •
        (fun u j =>
          (generatedTwelfthIncomingSpinTensorInputInteger (nortonUIntegerLabel u) j : ℝ)) := by
    ext u j
    have h := generatedTwelfth_incoming_tensor_input_actual u j
    change _ = (1 / (16 * Real.sqrt 2)) * _
    field_simp [hsqrt]
    nlinarith [h]
  rw [generatedFourth_local_tensor, hsource, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [generatedTwelfth_incoming_candidate_tensor_integer]
  field_simp [hsqrt]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
