/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixActionGeneric

/-! Complete actual integral lattice-basis matrices for candidate2. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData02Matrix : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-1, -1, -1, 0, 2, -1, -1, 0, -3, -1, -1, -2, 2, -1, -1, 0, 0, 0, 1, -1, 3, -1, 0, -9],
    ![0, 0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 2],
    ![0, 1, 0, 0, -1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2],
    ![2, 1, 1, 1, 0, 1, 1, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1, 2],
    ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 2],
    ![0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, 1],
    ![0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 2],
    ![0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, -1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, -1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  ]

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData02Inverse : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-1, -1, -1, 0, 2, -1, -1, 0, -3, -1, -1, -2, 2, -1, -1, 0, 0, 0, 1, -1, 3, -1, 0, -9],
    ![0, 0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 2],
    ![0, 1, 0, 0, -1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2],
    ![2, 1, 1, 1, 0, 1, 1, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1, 2],
    ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 2],
    ![0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, 1],
    ![0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 2],
    ![0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, -1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, -1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  ]

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- Whole physical numerator and true denominator act on the complete actual integral basis. -/
theorem generatedTenth_axis_lower_recovery_lattice_basis_02 :
    generatedTenthAxisLowerRecoveryCompactSpatialNumerator 2 * leechBasisMatrix =
      (generatedTenthAxisLowerRecoveryCompactSpatialDenominator 2 : ℤ) •
        (leechBasisMatrix * generatedTenthAxisLowerRecoveryLatticeBasisData02Matrix) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- All24 original hyperbolic binary columns agree with the actual integral basis action. -/
theorem generatedTenth_axis_lower_recovery_lattice_binary_02 :
    ∀ j : Fin 24,
      (leechHyperbolicInverse * (generatedTenthAxisLowerRecoveryLatticeBasisData02Matrix).map
        (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ
          monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) =
            monsterCo1GeometryBinaryMaskDecode
              (generatedTenthAxisLowerRecoveryCompactBinaryColumns 2 j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
