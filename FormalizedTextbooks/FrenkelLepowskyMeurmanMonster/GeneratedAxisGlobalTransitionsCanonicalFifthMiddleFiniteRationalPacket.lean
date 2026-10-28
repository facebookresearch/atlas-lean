/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFifthMiddleShortPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRawMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality

/-! Complete finite rational coordinates and the actual squared norm of the Fifth middle axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The entire physical matrix, finite preferred short constituent, and zero actual tensor. -/
def generatedAxisGlobalCanonicalFifthMiddleFiniteRationalPacket :
    GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalFifthMiddleMatrixQ,
    (generatedAxisGlobalCanonicalFifthMiddleSparseShortQ, 0))

/-- Every coefficient is bound to the complete original genuine middle axis. -/
theorem generatedAxisGlobalCanonicalFifthMiddleFiniteRationalPacket_actual :
    griessConwayEncode generatedAxisGlobalCanonicalFifthMiddleAxis =
    generatedAxisGlobalRationalPacketReal
      generatedAxisGlobalCanonicalFifthMiddleFiniteRationalPacket := by
  apply Prod.ext
  · funext i j
    exact generatedAxisGlobalFifthMiddleMatrix_entry i j
  · apply Prod.ext
    · funext r
      exact (generatedAxisGlobalCanonicalFifthMiddleSparseShortQ_actual r).symm
    · change (griessConwayEncode (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.2 = _
      rw [generatedFifth_middle_tensor_zero]
      funext t i
      simp [generatedAxisGlobalRationalPacketReal,
        generatedAxisGlobalCanonicalFifthMiddleFiniteRationalPacket]

/-- The genuine middle axis has the full original squared Griess norm 128. -/
theorem generatedAxisGlobalCanonicalFifthMiddle_norm :
    griessForm generatedAxisGlobalCanonicalFifthMiddleAxis
      generatedAxisGlobalCanonicalFifthMiddleAxis = 128 := by
  rw [generatedAxisGlobalCanonicalFifthMiddleAxis, rhoLocal_form,
    sExtra_preserves_griessForm, generatedAxisGlobal_conwayShortAxis_norm]

/-- Its last original triality is the complete canonical Fifth axis. -/
theorem generatedAxisGlobalCanonicalFifthMiddle_triality :
    sExtra generatedAxisGlobalCanonicalFifthMiddleAxis = generatedFifthAxis := by
  rw [generatedFifthAxis_local_expression]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
