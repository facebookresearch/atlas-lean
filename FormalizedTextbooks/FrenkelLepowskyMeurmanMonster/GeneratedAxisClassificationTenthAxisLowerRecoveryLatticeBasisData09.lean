/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixActionGeneric

/-! Complete actual integral lattice-basis matrices for candidate9. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData09Matrix : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![15, 5, 7, 15, 1, 6, 9, -1, 15, 9, 5, 14, 14, 6, 7, 15, 10, 10, 9, 0, 9, 8, 6, 18],
    ![-3, -1, -1, -3, -1, -1, -2, 0, -3, -2, -1, -3, -3, -2, -2, -3, -2, -2, -2, 0, -2, -2, -2, -4],
    ![-3, -1, -2, -3, -1, -1, -2, -1, -3, -2, -1, -3, -2, -1, -2, -3, -2, -2, -2, -1, -2, -2,
      -1, -4],
    ![-4, -1, -2, -4, 0, -2, -2, 0, -4, -2, -1, -3, -3, -1, -1, -3, -2, -2, -2, 1, -1, -1, 0, -4],
    ![-5, -2, -2, -4, -1, -2, -3, 0, -4, -3, -2, -3, -4, -2, -2, -4, -3, -2, -2, 0, -2, -2, -1, -5],
    ![-3, -1, -1, -2, 0, -1, -2, 1, -3, -1, -1, -2, -3, -1, -1, -2, -2, -1, -1, 1, -1, -1, -1, -3],
    ![-2, 0, -1, -2, 0, -1, -1, 1, -3, -1, 0, -2, -2, -1, -1, -2, -2, -2, -2, 0, -2, -1, -1, -3],
    ![2, 0, 1, 1, 1, 1, 1, 0, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 2],
    ![-3, -1, -2, -3, 0, -1, -2, 0, -3, -2, -1, -3, -3, -1, -2, -3, -2, -2, -1, 0, -2, -2, -1, -3],
    ![-1, 0, 0, -2, 1, 0, -1, 1, -2, -1, 0, -2, -1, 0, 0, -2, -1, -2, -1, 0, -1, -1, -1, -2],
    ![-3, -1, -2, -3, 0, -1, -2, 0, -3, -2, -1, -3, -3, -1, -2, -3, -2, -2, -2, -1, -2, -2, -1, -4],
    ![1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    ![-3, -1, -1, -3, -1, -1, -2, 0, -2, -2, -1, -2, -3, -1, -1, -3, -3, -2, -2, -1, -2, -2, -2,
      -3],
    ![1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1],
    ![1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1],
    ![1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1],
    ![-2, -1, -1, -3, 0, -1, -1, 0, -2, -1, -1, -3, -2, -1, -1, -3, -1, -2, -2, 0, -2, -1, -1, -3],
    ![0, 0, 0, 0, -1, 0, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0],
    ![2, 1, 1, 2, 0, 1, 1, 0, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 0, 1, 1, 0, 2],
    ![0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1],
    ![2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 0, 1, 1, 1, 2],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![2, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 2],
    ![-2, -1, -1, -2, 0, -1, -1, 0, -2, -1, -1, -2, -2, -1, -1, -2, -1, -1, -1, 0, -1, -1, -1, -2]
  ]

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData09Inverse : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![3, 0, 1, 0, 0, -1, 2, -1, 10, 6, 6, 4, -1, -1, 9, -1, 2, 4, -3, 5, 1, 2, 0, -5],
    ![-1, 0, -1, 0, -1, 0, -1, -1, -2, -1, -2, -1, 0, 0, -3, 0, -1, -1, 0, -2, -1, -1, -1, 0],
    ![-1, 1, 0, 0, 0, 0, -1, 1, -2, -1, -2, 0, 0, 1, -2, 0, -1, 0, 0, -1, 1, 0, 0, 1],
    ![-2, -1, 0, -1, -1, 0, -1, 0, -3, -2, -2, -1, 0, 0, -2, 0, -1, -1, 0, -1, 0, 0, 0, 0],
    ![-1, 0, -1, 0, 0, 0, -1, 0, -2, -2, -1, -1, 0, 0, -2, 0, -1, -1, 1, -2, 0, -1, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1, 1, 0, -1, 1, 0, -1, 1, -1, -1, 0, 1, 1],
    ![-1, 0, 0, 0, 0, 0, 0, 1, -2, -1, -1, 0, 0, 1, -1, 1, -1, 0, 1, 0, 0, 0, 1, 2],
    ![1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![-1, 0, -1, 0, 0, 0, -1, 0, -2, -2, -1, -1, 0, 0, -2, 0, 0, -1, 1, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, -2, -1, -1, -1, 0, 0, -2, 0, 0, -1, 0, -1, -1, -1, 0, 1],
    ![-1, 0, 0, 0, 0, 0, 0, 1, -2, -2, -1, -1, 0, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 1],
    ![1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0, 0, -1, 1, -1, 0, -1, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0],
    ![0, -1, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, -1, 0, -1, -1],
    ![1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1, -1, 0, 0, -2, 0, 0, -1, 0, -1, -1, 0, -1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, 1, 0, -1, 0, 0, -1, 0, -1, 0, 0, 0, 1]
  ]

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- Whole physical numerator and true denominator act on the complete actual integral basis. -/
theorem generatedTenth_axis_lower_recovery_lattice_basis_09 :
    generatedTenthAxisLowerRecoveryCompactSpatialNumerator 9 * leechBasisMatrix =
      (generatedTenthAxisLowerRecoveryCompactSpatialDenominator 9 : ℤ) •
        (leechBasisMatrix * generatedTenthAxisLowerRecoveryLatticeBasisData09Matrix) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- All24 original hyperbolic binary columns agree with the actual integral basis action. -/
theorem generatedTenth_axis_lower_recovery_lattice_binary_09 :
    ∀ j : Fin 24,
      (leechHyperbolicInverse * (generatedTenthAxisLowerRecoveryLatticeBasisData09Matrix).map
        (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ
          monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) =
            monsterCo1GeometryBinaryMaskDecode
              (generatedTenthAxisLowerRecoveryCompactBinaryColumns 9 j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
