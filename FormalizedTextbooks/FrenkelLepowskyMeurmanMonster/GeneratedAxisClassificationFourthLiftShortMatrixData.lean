/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortHom

/-! Literal binary and full central-bit data for a certified actual extraspecial homomorphism. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Literal binary columns, before comparison with the actual corrected spin conjugation. -/
def generatedFourthLiftQBinaryColumns : Fin 24 → ℕ := ![
    57344, 7000064, 7976960, 5994496, 655388, 3012650, 2146368, 3303553, 180492, 2861574,
    10539088, 4194304, 659470, 534541, 3096587, 2457607, 67584, 131072, 4458496, 524288,
    1048576, 2097152, 4196352, 8584209]

/-- The complete literal matrix on the actual extraspecial binary quotient. -/
def generatedFourthLiftQBinaryMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => golayBooleanCast ((generatedFourthLiftQBinaryColumns j).testBit i.val)

/-- Literal central polynomial rows, including all twenty-four diagonal phase bits. -/
def generatedFourthLiftQPhaseRows : Fin 24 → ℕ := ![
    4097, 8192, 8406020, 8422408, 160, 62048, 49216, 25216, 49920, 8431104, 4521984, 8388608,
    8450048, 57344, 8421376, 8421376, 8454144, 0, 8388608, 0, 0, 0, 12582912, 8388608]

/-- The full central-bit quadratic matrix of the candidate actual Q homomorphism. -/
def generatedFourthLiftQPhaseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => golayBooleanCast ((generatedFourthLiftQPhaseRows i).testBit j.val)

set_option maxHeartbeats 8000000 in
-- Verify every one of the 576 genuine extraspecial cocycle coefficients.
/-- The literal binary and central matrices preserve the actual Q multiplication law. -/
theorem generatedFourth_lift_q_matrix_certificate :
    ∀ i j : Fin 24,
      qBeta (generatedFourthLiftQBinaryMatrix.col i) (generatedFourthLiftQBinaryMatrix.col j) =
        qBeta (Pi.single i 1) (Pi.single j 1) +
          generatedFourthLiftQPhaseMatrix i j + generatedFourthLiftQPhaseMatrix j i := by
  decide +kernel

/-- A genuine actual Q homomorphism; its equality to the spin action is a separate theorem. -/
def generatedFourthLiftShortMatrixHom : Q →* Q :=
  generatedFourthLiftQMatrixHom generatedFourthLiftQBinaryMatrix generatedFourthLiftQPhaseMatrix
    (by simpa only [Matrix.mulVec_single_one] using generatedFourth_lift_q_matrix_certificate)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
