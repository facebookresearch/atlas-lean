/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFrame
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFrameCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalMatrixShort

/-! Every original root-six positive matrix coordinate is bound to the actual octad projection under its genuine frame. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- Actual full original matrix and short source bindings determine the entire outgoing physical matrix. -/
theorem generatedAxisGlobalOddRoot06PositiveMatrix_actual :
    (griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis))).1 =
      (generatedAxisGlobalRationalTriality (generatedAxisGlobalOddSparseRootPacket 1)).1.map
        (Rat.castHom ℝ) := by
  apply generatedAxisGlobalRationalMatrixShort_actual
  · change (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)).1 =
      (generatedAxisGlobalOddRootMatrixQ 6).map (Rat.castHom ℝ)
    exact generatedAxisGlobalOddRootMatrix_actual 6
  · intro r
    change (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)).2.1 r =
      (generatedAxisGlobalOddSparseShortQ 1 r : ℝ)
    rw [generatedAxisGlobalOddRootShortQ_actual, generatedAxisGlobalOddSparseShortQ_root06]

/-- The complete outgoing original matrix becomes the certified octad coordinate projection under its actual frame. -/
theorem generatedAxisGlobalOddRoot06PositiveOctadProjection_actual :
    conwayMatrixAction generatedAxisGlobalOddRoot06OctadFrameIsometry
      (griessConwayEncode
        (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis))).1 =
      Matrix.diagonal (fun i : Fin 24 =>
        if (0x714281 : ℕ).testBit i.val then (1 : ℝ) else 0) := by
  rw [conwayMatrixAction_eq_conjugate, generatedAxisGlobalOddRoot06OctadFrame_actual,
    generatedAxisGlobalOddRoot06PositiveMatrix_actual]
  have h := congrArg (Rat.castHom ℝ).mapMatrix generatedAxisGlobalOddRoot06OctadMatrix_conjugation
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at h
  rw [← h]
  ext i j
  simp only [Matrix.map_apply, generatedAxisGlobalOddRoot06OctadMatrix_certificate,
    Matrix.diagonal_apply]
  split_ifs <;> simp_all

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
