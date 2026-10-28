/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhQSupportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisCharacters

/-! Exact binary projection certificates restrict genuine original Q fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Exact original hyperbolic phase covectors of the selected preferred short lifts. -/
def generatedEleventhQSupportCovectorMask : Fin 21 → ℕ :=
  ![1536, 8390144, 1280, 1792, 1039, 143, 79, 1035, 491, 923, 1031, 3715469, 8405003, 46084,
      12084073, 11929183, 3597067, 3961163, 91977, 2622483, 16119573]

/-- Actual characteristic-two phase equations in the original quotient coordinates. -/
def generatedEleventhQSupportPhaseMatrix : Matrix (Fin 21) (Fin 24) (ZMod 2) :=
  fun j => monsterCo1GeometryBinaryMaskDecode (generatedEleventhQSupportCovectorMask j)

/-- Original free quotient coordinates of the complete selected phase system. -/
def generatedEleventhQSupportFree : Fin 3 → Fin 24 :=
  ![11, 20, 22]

/-- Rows of the exact inverse of all selected phases followed by the original free coordinates. -/
def generatedEleventhQSupportInverseMask : Fin 24 → ℕ :=
  ![4729356, 4730513, 144, 1040, 693, 484, 93, 61, 9, 12, 13, 2097152, 111212, 30984, 4238,
      125945, 4999119, 9755913, 4971798, 9929933, 4194304, 10453736, 8388608, 3]

/-- The exact inverse projection onto the selected phase equations. -/
def generatedEleventhQSupportPhaseProjection : Matrix (Fin 24) (Fin 21) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode
    (generatedEleventhQSupportInverseMask i) (⟨j.val, by omega⟩ : Fin 24)

/-- The exact inverse projection onto the remaining original quotient coordinates. -/
def generatedEleventhQSupportFreeProjection : Matrix (Fin 24) (Fin 3) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode
    (generatedEleventhQSupportInverseMask i) (⟨21 + j.val, by omega⟩ : Fin 24)

/-- Selection of the remaining genuine original quotient coordinates. -/
def generatedEleventhQSupportFreeMatrix : Matrix (Fin 3) (Fin 24) (ZMod 2) :=
  fun i j => if generatedEleventhQSupportFree i = j then 1 else 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
-- Verify every original binary entry of the inverse projection identity.
/-- The complete original phase and free projections reconstruct every quotient vector. -/
theorem generatedEleventh_Q_support_projection_certificate :
    generatedEleventhQSupportPhaseProjection * generatedEleventhQSupportPhaseMatrix +
      generatedEleventhQSupportFreeProjection * generatedEleventhQSupportFreeMatrix = 1 := by
  decide +kernel

/-- Vanishing of all original selected phases determines the quotient by its free coordinates. -/
theorem generatedEleventh_Q_support_free_determines (v : Fin 24 → ZMod 2)
    (hv : generatedEleventhQSupportPhaseMatrix *ᵥ v = 0) :
    generatedEleventhQSupportFreeProjection *ᵥ
      (generatedEleventhQSupportFreeMatrix *ᵥ v) = v := by
  have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) (ZMod 2) => M *ᵥ v)
    generatedEleventh_Q_support_projection_certificate
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero, zero_add, Matrix.one_mulVec] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
