/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisCharacters

/-! Exact binary projection certificates restrict genuine original Q fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original twenty-four binary source bits of a literal natural mask. -/
def generatedFifthRootEightBinaryMaskDecode (m : ℕ) (j : Fin 24) : ZMod 2 :=
  if m.testBit j.val then 1 else 0

/-- Exact original hyperbolic phase covectors of the selected preferred short lifts. -/
def generatedFifthRootEightQSupportCovectorMask : Fin 22 → ℕ :=
  ![1536, 8390144, 1280, 1792, 1038, 62, 923, 635, 1031, 527, 1679, 1615, 3449759, 3461575,
    8396813, 4130812, 12083556, 4186893, 3437133, 6591298, 8131635, 881779]

/-- Actual characteristic-two phase equations in the original quotient coordinates. -/
def generatedFifthRootEightQSupportPhaseMatrix : Matrix (Fin 22) (Fin 24) (ZMod 2) :=
  fun j => generatedFifthRootEightBinaryMaskDecode (generatedFifthRootEightQSupportCovectorMask j)

/-- Original free quotient coordinates of the complete selected phase system. -/
def generatedFifthRootEightQSupportFree : Fin 2 → Fin 24 :=
  ![11, 17]

/-- Rows of the exact inverse of all selected phases followed by the original free coordinates. -/
def generatedFifthRootEightQSupportInverseMask : Fin 24 → ℕ :=
  ![529, 2988, 2224, 769, 3316, 3273, 2573, 1549, 9, 12, 13, 4194304, 449747, 18851, 434308,
    288518, 2353016, 8388608, 10782629, 10966697, 12269958, 1804406, 11908514, 3]

/-- The exact inverse projection onto the selected phase equations. -/
def generatedFifthRootEightQSupportPhaseProjection : Matrix (Fin 24) (Fin 22) (ZMod 2) :=
  fun i j => generatedFifthRootEightBinaryMaskDecode
    (generatedFifthRootEightQSupportInverseMask i) (⟨j.val, by omega⟩ : Fin 24)

/-- The exact inverse projection onto the remaining original quotient coordinates. -/
def generatedFifthRootEightQSupportFreeProjection : Matrix (Fin 24) (Fin 2) (ZMod 2) :=
  fun i j => generatedFifthRootEightBinaryMaskDecode
    (generatedFifthRootEightQSupportInverseMask i) (⟨22 + j.val, by omega⟩ : Fin 24)

/-- Selection of the remaining genuine original quotient coordinates. -/
def generatedFifthRootEightQSupportFreeMatrix : Matrix (Fin 2) (Fin 24) (ZMod 2) :=
  fun i j => if generatedFifthRootEightQSupportFree i = j then 1 else 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
-- Verify every original binary entry of the inverse projection identity.
/-- The original phase and free projections reconstruct every quotient vector. -/
theorem generatedFifthRootEight_Q_support_projection_certificate :
    generatedFifthRootEightQSupportPhaseProjection * generatedFifthRootEightQSupportPhaseMatrix +
      generatedFifthRootEightQSupportFreeProjection *
        generatedFifthRootEightQSupportFreeMatrix = 1 := by
  decide +kernel

/-- Vanishing of all original selected phases determines the quotient by its free coordinates. -/
theorem generatedFifthRootEight_Q_support_free_determines (v : Fin 24 → ZMod 2)
    (hv : generatedFifthRootEightQSupportPhaseMatrix *ᵥ v = 0) :
    generatedFifthRootEightQSupportFreeProjection *ᵥ
      (generatedFifthRootEightQSupportFreeMatrix *ᵥ v) = v := by
  have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) (ZMod 2) => M *ᵥ v)
    generatedFifthRootEight_Q_support_projection_certificate
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero, zero_add, Matrix.one_mulVec] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
