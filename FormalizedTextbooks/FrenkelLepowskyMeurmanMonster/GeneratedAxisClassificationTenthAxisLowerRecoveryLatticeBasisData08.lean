/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixActionGeneric

/-! Complete actual integral lattice-basis matrices for candidate8. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData08Matrix : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-9, 4, 3, -9, 4, -8, -11, 6, -3, -13, -11, -4, 3, 4, 3, -9, -3, -9, -8, -2, 20, 1, 6, 0],
    ![1, -1, -1, 2, -1, 1, 2, -1, 0, 2, 2, 1, -1, -1, -1, 2, 0, 2, 2, 1, -4, 0, -1, 0],
    ![2, 0, 0, 2, 0, 2, 2, 0, 0, 3, 2, 1, 0, 0, 0, 2, 1, 2, 2, 1, -3, 1, 0, 1],
    ![2, -1, -1, 2, -1, 1, 2, -2, 0, 3, 2, 0, -1, -2, -2, 1, 1, 1, 1, 0, -5, -1, -2, -1],
    ![1, -1, -1, 2, -1, 1, 2, -1, 1, 3, 2, 2, -1, 0, 0, 2, 0, 3, 2, 1, -3, 0, -1, 0],
    ![1, -2, -1, 1, -1, 1, 2, -2, 1, 2, 1, 0, -1, -1, -1, 1, 0, 1, 1, 0, -4, -1, -2, -1],
    ![2, -1, -1, 2, -1, 2, 3, -1, 1, 2, 2, 0, 0, -1, 0, 2, 1, 2, 2, 0, -4, 0, -1, 0],
    ![0, 1, 1, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, -1, -1, -1, 1, 0, 0, 0],
    ![1, -1, -1, 1, -1, 1, 1, -2, 0, 2, 2, 1, -1, -1, -1, 1, 0, 1, 1, 0, -4, -1, -1, 0],
    ![2, -1, 0, 2, -1, 2, 2, -1, 0, 2, 2, 0, 0, -1, -1, 2, 1, 1, 1, 0, -4, 0, -1, 0],
    ![3, 0, 0, 2, 0, 2, 3, -1, 1, 3, 3, 1, 0, -1, 0, 2, 1, 1, 1, 0, -4, 0, -1, 0],
    ![-1, 0, 0, -1, 0, -1, -1, 0, 1, -1, -1, 0, 0, 1, 1, -1, 0, 0, 0, 0, 2, 0, 0, 0],
    ![3, 0, 1, 2, 0, 2, 3, 0, 2, 3, 3, 2, 0, 0, 1, 2, 1, 2, 2, 1, -3, 1, -1, 2],
    ![-1, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0, 1, 0, 0, -1],
    ![-1, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0, -1, -1, 0, 1, 0, 0, -1],
    ![-2, 0, -1, -1, 0, -1, -2, 0, -1, -1, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 2, 0, 1, 0],
    ![1, -1, -1, 1, -1, 1, 1, -2, 0, 2, 2, 0, -1, -1, -1, 1, 0, 1, 1, 0, -4, -1, -2, -1],
    ![0, 1, 1, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 2, 1, 1, 1],
    ![0, 1, 1, 0, 1, 0, 0, 2, 0, -1, -1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1],
    ![-1, 0, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 1, 0, 0, 0, 0, -1, -1, -1, 1, 0, 0, 0],
    ![-1, 0, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, -1, -1, -1, -1, -1, 1, -1, 0, -1],
    ![-1, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0, -1, -1, 0, 1, 0, 1, 0],
    ![2, 0, 0, 2, 0, 2, 2, 0, 1, 2, 2, 1, 0, 0, 0, 2, 1, 2, 2, 1, -2, 0, 0, 1]
  ]

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData08Inverse : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![13, -2, -3, 16, 13, 14, 14, 14, 9, 12, 11, 5, 3, 7, 6, 16, 7, 8, 23, 14, -5, -2, 9, 14],
    ![-3, 1, 1, -3, -3, -3, -3, -2, -2, -3, -2, 0, -1, -1, -1, -3, -1, -1, -4, -2, 2, 1, -1, -2],
    ![-2, 1, 1, -3, -2, -2, -3, -2, -2, -2, -2, -1, 0, -1, -1, -3, -1, -2, -4, -3, 1, 1, -1, -2],
    ![-2, 1, 1, -3, -2, -3, -3, -3, -2, -2, -2, -1, -1, -2, -2, -4, -1, -2, -5, -3, 1, 0, -2, -3],
    ![-3, 0, 0, -4, -3, -3, -4, -4, -2, -3, -2, -2, -1, -2, -2, -4, -2, -3, -5, -4, 0, -1, -3, -4],
    ![-2, 0, 1, -3, -2, -2, -2, -2, -1, -2, -2, -1, -1, -1, -1, -3, -1, -1, -4, -2, 1, 0, -2, -2],
    ![-2, 1, 1, -3, -2, -2, -2, -2, -1, -3, -2, -1, 0, -1, 0, -3, -1, -1, -4, -3, 2, 1, -1, -2],
    ![0, -1, -1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, -1, 0, 0, 0],
    ![-3, 0, 0, -3, -3, -3, -3, -3, -3, -2, -2, -1, -1, -2, -2, -3, -2, -2, -5, -2, 0, 0, -2, -3],
    ![-2, 0, 1, -2, -2, -2, -2, -2, -2, -2, -2, -1, 0, -1, -1, -2, -1, -1, -4, -2, 1, 1, -1, -2],
    ![-2, 0, 0, -3, -2, -3, -2, -3, -2, -2, -2, -2, 0, -2, -1, -3, -1, -2, -5, -3, 0, 0, -2, -3],
    ![1, 0, 0, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 1, 1, 1, 0, 1, 2, 1, 0, 0, 0, 1],
    ![-2, 0, 1, -3, -2, -3, -2, -3, -1, -2, -2, -1, 0, -1, 0, -3, -1, -2, -4, -2, 1, 1, -2, -2],
    ![1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 2, 1, 0, 0, 1, 1],
    ![1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 2, 1, 0, 0, 1, 1],
    ![0, 0, -1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 0, 1, 1],
    ![-3, 0, 0, -3, -3, -3, -3, -3, -1, -2, -2, 0, -1, -1, -1, -3, -2, -1, -4, -3, 1, 0, -2, -3],
    ![0, -1, -1, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 1, 0, -1, -1, 0, 0],
    ![2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 0, 1, 1, 2],
    ![1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 2, 2, 0, 0, 1, 2],
    ![2, 0, 0, 2, 2, 2, 2, 2, 1, 1, 1, 0, 1, 1, 1, 2, 1, 1, 2, 1, 0, 0, 1, 2],
    ![1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, -1, -1, 0, 0],
    ![1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, -1, 0, 1, 1],
    ![-2, 0, 0, -2, -2, -2, -2, -2, -1, -2, -2, -1, 0, -1, -1, -2, -1, -1, -3, -2, 1, 0, -1, -2]
  ]

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- Whole physical numerator and true denominator act on the complete actual integral basis. -/
theorem generatedTenth_axis_lower_recovery_lattice_basis_08 :
    generatedTenthAxisLowerRecoveryCompactSpatialNumerator 8 * leechBasisMatrix =
      (generatedTenthAxisLowerRecoveryCompactSpatialDenominator 8 : ℤ) •
        (leechBasisMatrix * generatedTenthAxisLowerRecoveryLatticeBasisData08Matrix) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- All24 original hyperbolic binary columns agree with the actual integral basis action. -/
theorem generatedTenth_axis_lower_recovery_lattice_binary_08 :
    ∀ j : Fin 24,
      (leechHyperbolicInverse * (generatedTenthAxisLowerRecoveryLatticeBasisData08Matrix).map
        (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ
          monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) =
            monsterCo1GeometryBinaryMaskDecode
              (generatedTenthAxisLowerRecoveryCompactBinaryColumns 8 j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
