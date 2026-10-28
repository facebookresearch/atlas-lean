/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQSupportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisCharacters

/-! Exact binary projection certificates restrict genuine original Q fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Exact original hyperbolic phase covectors of the selected preferred short lifts. -/
def generatedTenthQSupportCovectorMask : Fin 23 → ℕ :=
  ![1792, 8390400, 1039, 143, 79, 207, 46, 30, 1037, 685, 923, 1508, 16445595, 16117819, 8443344,
      10286806, 1836057, 12076738, 11859866, 3441093, 12121958, 4391675, 13238541]

/-- Actual characteristic-two phase equations in the original quotient coordinates. -/
def generatedTenthQSupportPhaseMatrix : Matrix (Fin 23) (Fin 24) (ZMod 2) :=
  fun j => monsterCo1GeometryBinaryMaskDecode (generatedTenthQSupportCovectorMask j)

/-- Original free quotient coordinates of the complete selected phase system. -/
def generatedTenthQSupportFree : Fin 1 → Fin 24 :=
  ![11]

/-- Rows of the exact inverse of all selected phases followed by the original free coordinates. -/
def generatedTenthQSupportInverseMask : Fin 24 → ℕ :=
  ![3992, 260, 2837, 1457, 3872, 4064, 40, 48, 3281, 3308, 60, 8388608, 1984545, 118553, 1279195,
      888620, 3151612, 2369360, 4461175, 5250059, 1379145, 5545558, 3421877, 3]

/-- The exact inverse projection onto the selected phase equations. -/
def generatedTenthQSupportPhaseProjection : Matrix (Fin 24) (Fin 23) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode
    (generatedTenthQSupportInverseMask i) (⟨j.val, by omega⟩ : Fin 24)

/-- The exact inverse projection onto the remaining original quotient coordinates. -/
def generatedTenthQSupportFreeProjection : Matrix (Fin 24) (Fin 1) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode
    (generatedTenthQSupportInverseMask i) (⟨23 + j.val, by omega⟩ : Fin 24)

/-- Selection of the remaining genuine original quotient coordinates. -/
def generatedTenthQSupportFreeMatrix : Matrix (Fin 1) (Fin 24) (ZMod 2) :=
  fun i j => if generatedTenthQSupportFree i = j then 1 else 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
-- Verify every original binary entry of the inverse projection identity.
/-- The complete original phase and free projections reconstruct every quotient vector. -/
theorem generatedTenth_Q_support_projection_certificate :
    generatedTenthQSupportPhaseProjection * generatedTenthQSupportPhaseMatrix +
      generatedTenthQSupportFreeProjection * generatedTenthQSupportFreeMatrix = 1 := by
  decide +kernel

/-- Vanishing of all original selected phases determines the quotient by its free coordinates. -/
theorem generatedTenth_Q_support_free_determines (v : Fin 24 → ZMod 2)
    (hv : generatedTenthQSupportPhaseMatrix *ᵥ v = 0) :
    generatedTenthQSupportFreeProjection *ᵥ
      (generatedTenthQSupportFreeMatrix *ᵥ v) = v := by
  have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) (ZMod 2) => M *ᵥ v)
    generatedTenth_Q_support_projection_certificate
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero, zero_add, Matrix.one_mulVec] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
