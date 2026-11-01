/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixActionGeneric

/-! Complete actual integral lattice-basis matrices for candidate10. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData10Matrix : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-12, -16, -12, -9, -12, -1, -1, -15, 4, -8, -5, -12, -7, -9, 2, -1, -5, -1, -2, -6, -12,
      -9, -5, -23],
    ![2, 3, 2, 2, 2, 0, 0, 3, -2, 1, 1, 2, 1, 1, -1, 0, 1, 0, 0, 1, 2, 1, 1, 4],
    ![3, 3, 2, 2, 2, 1, 0, 2, 0, 2, 1, 2, 2, 2, -1, 0, 1, 0, 0, 0, 2, 1, 0, 4],
    ![1, 3, 2, 1, 2, 0, -1, 3, -2, 1, 0, 2, 1, 2, -1, 0, 0, 0, 0, 1, 3, 2, 1, 4],
    ![4, 4, 3, 2, 3, 1, 1, 3, 0, 2, 2, 2, 2, 2, 0, 0, 2, 0, 1, 1, 2, 2, 1, 6],
    ![2, 3, 3, 1, 2, 0, 0, 3, -1, 1, 1, 2, 1, 1, 0, 0, 1, 0, 0, 1, 2, 2, 1, 4],
    ![3, 4, 3, 2, 3, 0, 0, 3, 0, 2, 1, 3, 2, 3, 0, 0, 1, 0, 0, 1, 3, 2, 1, 5],
    ![-2, -2, -2, -1, -1, -1, 0, -1, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, -1, 0, -2],
    ![2, 3, 2, 1, 2, 0, 1, 3, -1, 1, 1, 2, 1, 1, 0, 0, 1, 0, 0, 1, 2, 2, 1, 4],
    ![2, 3, 2, 2, 2, 0, 0, 3, -1, 2, 1, 3, 2, 2, 0, 1, 0, 0, 0, 1, 2, 2, 1, 4],
    ![2, 3, 2, 2, 2, 0, 0, 3, 0, 2, 1, 3, 1, 2, 0, 1, 1, 1, 1, 2, 3, 2, 1, 5],
    ![0, -1, 0, -1, 0, 0, 1, -1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1],
    ![3, 3, 2, 2, 2, 0, 1, 2, 0, 2, 1, 2, 1, 1, -1, 0, 1, 0, 0, 0, 1, 1, 0, 4],
    ![-2, -2, -1, -1, -1, 0, -1, -1, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, -2],
    ![-2, -2, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, -1, 0, -2],
    ![-1, -1, -1, -1, -1, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, -1, 0, 0, 0, 0, -1, -1, 0, -2],
    ![1, 2, 2, 1, 2, 0, 0, 3, -1, 1, 0, 2, 1, 2, 0, 0, 1, 1, 1, 2, 3, 2, 2, 4],
    ![0, -1, -1, 0, -1, 0, 0, -2, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1],
    ![0, -1, -1, 0, -1, 0, 0, -2, 0, 0, 0, -1, 0, -1, -1, 0, 0, -1, -1, -1, -2, -1, -1, -2],
    ![-1, -1, -1, -1, -1, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0, 0, 0, 0, -1, -1, -1, 0, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![-1, -1, -1, -1, -1, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1],
    ![-1, -1, -1, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1, -2],
    ![2, 2, 2, 2, 2, 0, 0, 2, 0, 1, 1, 2, 1, 1, 0, 0, 1, 0, 1, 1, 2, 1, 0, 3]
  ]

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData10Inverse : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![21, 20, 19, 16, 4, 2, 4, 2, 3, 10, 10, 16, 11, -6, 3, -1, 10, -7, -1, -2, 7, 12, -8, 9],
    ![-5, -5, -5, -3, -1, -1, -1, -1, -1, -3, -2, -4, -3, 0, -1, 0, -3, 1, 0, 0, -2, -4, 1, -3],
    ![-4, -4, -4, -3, -1, 0, -1, -1, -1, -2, -2, -3, -2, 1, -1, 0, -2, 1, 0, 0, -2, -3, 1, -2],
    ![-5, -4, -5, -4, -1, -1, -1, -1, -1, -2, -3, -4, -2, 2, -1, 0, -2, 2, 0, 0, -1, -2, 2, -2],
    ![-6, -5, -4, -4, -2, -1, -1, 0, -1, -3, -3, -3, -3, 1, 0, 0, -3, 2, 0, 1, -1, -2, 2, -2],
    ![-4, -4, -3, -3, -1, -1, -1, -1, 0, -2, -2, -3, -2, 1, 0, 0, -2, 1, 0, 0, -1, -2, 1, -2],
    ![-4, -4, -4, -3, -1, -1, -1, -1, 0, -2, -2, -3, -2, 1, -1, 0, -2, 1, 0, 0, -2, -3, 1, -2],
    ![2, 2, 2, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, -1, 0, 0, 1, 1, 0, 1],
    ![-4, -4, -3, -3, -1, 0, -1, 0, -1, -2, -2, -3, -2, 1, -1, 0, -2, 1, 0, 0, -1, -2, 1, -2],
    ![-3, -3, -3, -2, 0, 0, -1, 0, 0, -1, -1, -2, -1, 2, 0, 1, -1, 2, 1, 1, 0, -2, 2, -1],
    ![-4, -3, -3, -3, -1, 0, -1, 0, -1, -1, -2, -2, -2, 2, -1, 1, -2, 2, 0, 1, -1, -1, 2, -1],
    ![2, 1, 2, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, -1, 1, 0, 1, -1, 0, 0, 0, 1, -1, 1],
    ![-4, -4, -3, -3, -1, 0, -1, 0, -1, -2, -2, -3, -3, 0, -1, 0, -2, 1, 0, 0, -2, -3, 1, -2],
    ![2, 2, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 1],
    ![2, 2, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, -1, 0],
    ![-3, -3, -3, -3, 0, 0, 0, 0, 0, -2, -1, -3, -2, 1, 0, 0, -1, 1, 1, 1, -1, -2, 2, -1],
    ![0, 1, 1, 0, -1, 0, 0, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0],
    ![2, 1, 1, 2, 1, 0, 0, 0, 0, 1, 1, 1, 1, -1, 0, 0, 1, -1, 0, 0, 0, 0, -1, 1],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, -1, 0],
    ![2, 2, 2, 2, 0, 0, 0, 0, 1, 1, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 1],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 1],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0],
    ![-2, -2, -2, -2, 0, 0, 0, 0, 0, -1, -1, -2, -1, 1, 0, 0, -1, 1, 0, 0, -1, -1, 1, -1]
  ]

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- Whole physical numerator and true denominator act on the complete actual integral basis. -/
theorem generatedTenth_axis_lower_recovery_lattice_basis_10 :
    generatedTenthAxisLowerRecoveryCompactSpatialNumerator 10 * leechBasisMatrix =
      (generatedTenthAxisLowerRecoveryCompactSpatialDenominator 10 : ℤ) •
        (leechBasisMatrix * generatedTenthAxisLowerRecoveryLatticeBasisData10Matrix) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- All24 original hyperbolic binary columns agree with the actual integral basis action. -/
theorem generatedTenth_axis_lower_recovery_lattice_binary_10 :
    ∀ j : Fin 24,
      (leechHyperbolicInverse * (generatedTenthAxisLowerRecoveryLatticeBasisData10Matrix).map
        (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ
          monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) =
            monsterCo1GeometryBinaryMaskDecode
              (generatedTenthAxisLowerRecoveryCompactBinaryColumns 10 j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
