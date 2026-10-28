/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonPairingData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismPermutations

/-! An explicit original Golay permutation and Xi inverse carrying the root-six projection to an octad. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option autoImplicit false

/-- Exact involutive coordinate permutation of the original Golay code. -/
def generatedAxisGlobalOddRoot06OctadPermArray : Fin 24 → Fin 24 :=
  ![7, 2, 1, 4, 3, 6, 5, 0, 15, 10, 9, 12, 11, 14, 13, 8, 23, 18, 17, 20, 19, 22, 21, 16]

/-- Original Golay generator images of the coordinate permutation. -/
def generatedAxisGlobalOddRoot06OctadCodeImages : Fin 12 → Fin 4096 :=
  ![3069, 3070, 3015, 3019, 31, 47, 3145, 3205, 1290, 1542, 1087, 2048]

/-- Each original coordinate has the displayed inverse coordinate. -/
theorem generatedAxisGlobalOddRoot06OctadPerm_involution :
    ∀ i, generatedAxisGlobalOddRoot06OctadPermArray
      (generatedAxisGlobalOddRoot06OctadPermArray i) = i := by
  decide +kernel

/-- The literal array is a genuine permutation. -/
def generatedAxisGlobalOddRoot06OctadPermutation : Equiv.Perm (Fin 24) where
  toFun := generatedAxisGlobalOddRoot06OctadPermArray
  invFun := generatedAxisGlobalOddRoot06OctadPermArray
  left_inv := generatedAxisGlobalOddRoot06OctadPerm_involution
  right_inv := generatedAxisGlobalOddRoot06OctadPerm_involution

set_option maxHeartbeats 2000000 in
/-- All twelve original code-generator images are checked in the actual binary Golay encoder. -/
theorem generatedAxisGlobalOddRoot06OctadCode_certificate : ∀ j : Fin 12,
    golayPermute generatedAxisGlobalOddRoot06OctadPermutation
      (golayEncoder (Pi.single j 1)) =
      golayEncoder (golayLabelCoefficients (generatedAxisGlobalOddRoot06OctadCodeImages j)) := by
  decide +kernel

/-- Exact rational physical frame, original Xi inverse after the Golay coordinate permutation. -/
def generatedAxisGlobalOddRoot06OctadFrameQ : Matrix (Fin 24) (Fin 24) ℚ := fun i j =>
  co1XiMatrixQ (generatedAxisGlobalOddRoot06OctadPermArray j) i

/-- Complete conjugation with exact zero entries skipped before evaluating the original source matrix. -/
def generatedAxisGlobalOddRoot06OctadMatrixQ : Matrix (Fin 24) (Fin 24) ℚ := fun i j =>
  ∑ k : Fin 24,
    if generatedAxisGlobalOddRoot06OctadFrameQ i k = 0 then 0 else
      ∑ l : Fin 24, if generatedAxisGlobalOddRoot06OctadFrameQ j l = 0 then 0 else
        generatedAxisGlobalOddRoot06OctadFrameQ i k *
          (generatedAxisGlobalRationalTriality (generatedAxisGlobalOddSparseRootPacket 1)).1 k l *
          generatedAxisGlobalOddRoot06OctadFrameQ j l

/-- An existing original Golay permutation word carries the intermediate octad to the standard octad. -/
def generatedAxisGlobalOddRoot06OctadFinalGolayPermutation : golayAutomorphismSubgroup :=
  omegaOrbitGolayPermutation 0 * omegaOrbitGolayPermutation 0 *
    omegaOrbitGolayPermutation 1 * omegaOrbitGolayPermutation 0 *
      omegaOrbitGolayPermutation 1 * (omegaOrbitGolayPermutation 0)⁻¹ *
        omegaOrbitGolayPermutation 1

/-- Exact physical array of that existing original Golay permutation word. -/
def generatedAxisGlobalOddRoot06OctadFinalArray : Fin 24 → Fin 24 :=
  ![11, 16, 7, 0, 3, 18, 6, 9, 5, 13, 22, 4, 17, 21, 12, 19, 15, 1, 2, 20, 14, 8, 10, 23]

/-- Every coordinate of the complete original final permutation word is checked. -/
theorem generatedAxisGlobalOddRoot06OctadFinalArray_certificate : ∀ i : Fin 24,
    generatedAxisGlobalOddRoot06OctadFinalGolayPermutation.val i =
      generatedAxisGlobalOddRoot06OctadFinalArray i := by
  decide +kernel

/-- The complete physical frame places the root-six projection on the standard octad. -/
def generatedAxisGlobalOddRoot06OctadStandardFrameQ : Matrix (Fin 24) (Fin 24) ℚ := fun i j =>
  generatedAxisGlobalOddRoot06OctadFrameQ
    (generatedAxisGlobalOddRoot06OctadFinalGolayPermutation.val.symm i) j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
