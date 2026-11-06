/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFourthMiddleShortPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddNorm

/-! Complete finite rational coordinates and the actual squared norm of the Fourth middle axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The genuine original canonical local middle axis, before its last triality. -/
def generatedAxisGlobalCanonicalFourthMiddleAxis : GriessSpace :=
  rhoLocal (localFiberIntoH generatedFourthLocalFiber)
    (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))

/-- The entire physical matrix, finite preferred short constituent, and zero actual tensor. -/
def generatedAxisGlobalCanonicalFourthMiddleFiniteRationalPacket : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalCanonicalFourthMiddleMatrixQ,
    (generatedAxisGlobalCanonicalFourthMiddleSparseShortQ, 0))

/-- Every coefficient is bound to the complete original genuine middle axis. -/
theorem generatedAxisGlobalCanonicalFourthMiddleFiniteRationalPacket_actual :
    griessConwayEncode generatedAxisGlobalCanonicalFourthMiddleAxis =
    generatedAxisGlobalRationalPacketReal generatedAxisGlobalCanonicalFourthMiddleFiniteRationalPacket := by
  apply Prod.ext
  · funext i j
    exact generatedAxisGlobalCanonicalFourthMiddleMatrix_entry i j
  · apply Prod.ext
    · funext r
      exact (generatedAxisGlobalCanonicalFourthMiddleSparseShortQ_actual r).symm
    · change (griessConwayEncode (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.2 = _
      rw [generatedFourth_middle_tensor_zero]
      funext t i
      simp [generatedAxisGlobalRationalPacketReal,
        generatedAxisGlobalCanonicalFourthMiddleFiniteRationalPacket]

/-- The genuine middle axis has the full original squared Griess norm 128. -/
theorem generatedAxisGlobalCanonicalFourthMiddle_norm :
    griessForm generatedAxisGlobalCanonicalFourthMiddleAxis
      generatedAxisGlobalCanonicalFourthMiddleAxis = 128 := by
  rw [generatedAxisGlobalCanonicalFourthMiddleAxis, rhoLocal_form,
    sExtra_preserves_griessForm, generatedAxisGlobal_conwayShortAxis_norm]

/-- Its last original triality is the complete canonical Fourth axis. -/
theorem generatedAxisGlobalCanonicalFourthMiddle_triality :
    sExtra generatedAxisGlobalCanonicalFourthMiddleAxis = generatedFourthAxis := by
  rw [generatedFourthAxis_local_expression]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
