/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthQSupportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisCharacters

/-! Exact binary projection certificates restrict genuine original Q fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Exact original hyperbolic phase covectors of the selected preferred short lifts. -/
def generatedTwelfthQSupportCovectorMask : Fin 23 → ℕ :=
  ![1536, 8390144, 1280, 1792, 1035, 491, 923, 1152, 8, 8405003, 9109826, 8425513, 8819835,
      734360, 759010, 9147554, 5605036, 13993048, 841532, 4386831, 5371010, 4564922, 15271632]

/-- Actual characteristic-two phase equations in the original quotient coordinates. -/
def generatedTwelfthQSupportPhaseMatrix : Matrix (Fin 23) (Fin 24) (ZMod 2) :=
  fun j => monsterCo1GeometryBinaryMaskDecode (generatedTwelfthQSupportCovectorMask j)

/-- Original free quotient coordinates of the complete selected phase system. -/
def generatedTwelfthQSupportFree : Fin 1 → Fin 24 :=
  ![11]

/-- Rows of the exact inverse of all selected phases followed by the original free coordinates. -/
def generatedTwelfthQSupportInverseMask : Fin 24 → ℕ :=
  ![19849, 19604, 196846, 256, 213, 49338, 49155, 141, 9, 12, 13, 8388608, 2900137, 2943329, 542,
      2933913, 482165, 1225301, 1189402, 1401277, 959943, 6760312, 3530217, 3]

/-- The exact inverse projection onto the selected phase equations. -/
def generatedTwelfthQSupportPhaseProjection : Matrix (Fin 24) (Fin 23) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode
    (generatedTwelfthQSupportInverseMask i) (⟨j.val, by omega⟩ : Fin 24)

/-- The exact inverse projection onto the remaining original quotient coordinates. -/
def generatedTwelfthQSupportFreeProjection : Matrix (Fin 24) (Fin 1) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode
    (generatedTwelfthQSupportInverseMask i) (⟨23 + j.val, by omega⟩ : Fin 24)

/-- Selection of the remaining genuine original quotient coordinates. -/
def generatedTwelfthQSupportFreeMatrix : Matrix (Fin 1) (Fin 24) (ZMod 2) :=
  fun i j => if generatedTwelfthQSupportFree i = j then 1 else 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
-- Verify every original binary entry of the inverse projection identity.
/-- The complete original phase and free projections reconstruct every quotient vector. -/
theorem generatedTwelfth_Q_support_projection_certificate :
    generatedTwelfthQSupportPhaseProjection * generatedTwelfthQSupportPhaseMatrix +
      generatedTwelfthQSupportFreeProjection * generatedTwelfthQSupportFreeMatrix = 1 := by
  decide +kernel

/-- Vanishing of all original selected phases determines the quotient by its free coordinates. -/
theorem generatedTwelfth_Q_support_free_determines (v : Fin 24 → ZMod 2)
    (hv : generatedTwelfthQSupportPhaseMatrix *ᵥ v = 0) :
    generatedTwelfthQSupportFreeProjection *ᵥ
      (generatedTwelfthQSupportFreeMatrix *ᵥ v) = v := by
  have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) (ZMod 2) => M *ᵥ v)
    generatedTwelfth_Q_support_projection_certificate
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero, zero_add, Matrix.one_mulVec] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
