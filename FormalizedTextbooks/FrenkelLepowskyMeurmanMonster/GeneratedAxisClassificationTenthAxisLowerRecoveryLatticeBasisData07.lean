/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixActionGeneric

/-! Complete actual integral lattice-basis matrices for candidate7. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData07Matrix : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, -1, -1, 0, 2, 0, 2, -1, 1, 1, -1, -2, 1, 8, -8, 1, 4, -4, 3, 3, 3, 1, 4, -3],
    ![0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, -2, 2, 0, -1, 0, -1, 0, -1, 0, -1, 1],
    ![0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 1, 0, -1, 1, -1, -1, -1, 0, -1, 1],
    ![0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, -1, 1, -1, -1, -1, 0, -1, 1],
    ![-1, -1, 0, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -2, 2, -1, -1, 0, 0, 0, 0, -1, -1, 0],
    ![0, 0, 0, 0, -1, 0, -1, -1, 0, 0, 0, 0, 0, -2, 1, -1, -1, 0, -1, -2, -1, -1, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 2, 0, -1, 1, -1, 0, 0, 1, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, -1, 2, 0, -1, 1, 0, 0, 0, 0, 0, 1],
    ![-1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 1, -1, -1, 1, 0, -1, 2, 0, 0, 0, 0, -1, 0],
    ![0, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1],
    ![-1, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, -2, 1, 0, -2, 0, -1, -1, -1, -1, -1, 0],
    ![0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0],
    ![2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0, 1, -1, -1, -1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    ![0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0],
    ![0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
  ]

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData07Inverse : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-1, -2, 0, 1, 18, 0, -1, 16, -1, -2, -1, -1, -1, 6, 8, 0, 2, -6, 13, 12, 11, -1, 11, 4],
    ![0, 1, 0, 0, -4, 0, 0, -3, 0, 0, 0, 0, 0, -1, -2, 0, -1, 1, -3, -3, -2, 0, -2, -1],
    ![0, 1, 0, 0, -3, 0, 0, -2, 1, 0, 0, 1, 0, 0, -1, 0, -1, 2, -2, -2, -1, 0, -2, 0],
    ![1, 1, 0, 0, -3, 1, 1, -3, 1, 1, 1, 1, 1, 0, -1, 1, 0, 2, -2, -2, -2, 1, -1, 0],
    ![0, 0, 0, 0, -4, 0, 0, -3, 0, 0, 0, 0, 0, -2, -2, 0, -1, 1, -3, -3, -3, 0, -3, -1],
    ![-1, -1, -1, -1, -4, -1, 0, -4, -1, 0, 0, -1, 0, -2, -2, 0, -1, 0, -3, -2, -3, 0, -2, -2],
    ![0, 0, 0, -1, -4, 0, 0, -4, 0, 1, 0, 0, 0, -1, -2, 0, -1, 1, -3, -3, -3, 0, -3, -1],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0],
    ![0, 0, 0, 0, -4, 0, 0, -3, 0, 0, 0, 0, 0, -2, -2, 0, 0, 1, -3, -2, -2, 0, -2, -1],
    ![1, 1, 0, 0, -3, 0, 1, -3, 1, 1, 1, 1, 0, -1, -1, 0, 0, 1, -2, -2, -2, 0, -2, 0],
    ![0, 0, -1, 0, -3, 0, 0, -3, 0, 1, 0, 0, 0, -1, -2, 0, 0, 2, -2, -2, -2, 0, -2, -1],
    ![0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 1, 1, 0, 0, 0, 0],
    ![1, 1, 1, 0, -3, 0, 1, -2, 0, 1, 0, 0, 1, -1, -1, 0, 0, 1, -3, -2, -2, 1, -2, 0],
    ![0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 1, 1, 1, 0, 1, 0],
    ![0, 0, 0, 1, 1, 0, -1, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 1, -1, 0, 0],
    ![0, 0, 0, 0, -3, 0, 0, -3, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, -2, -2, -2, 0, -2, -1],
    ![0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1],
    ![0, 1, 1, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 2, 1, 1, 1],
    ![0, 0, 0, 0, 1, 0, 0, 1, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1, 0],
    ![0, -1, -1, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 1, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0],
    ![0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1],
    ![0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, -1, -1, -1, 0, -1, 0]
  ]

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- Whole physical numerator and true denominator act on the complete actual integral basis. -/
theorem generatedTenth_axis_lower_recovery_lattice_basis_07 :
    generatedTenthAxisLowerRecoveryCompactSpatialNumerator 7 * leechBasisMatrix =
      (generatedTenthAxisLowerRecoveryCompactSpatialDenominator 7 : ℤ) •
        (leechBasisMatrix * generatedTenthAxisLowerRecoveryLatticeBasisData07Matrix) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- All24 original hyperbolic binary columns agree with the actual integral basis action. -/
theorem generatedTenth_axis_lower_recovery_lattice_binary_07 :
    ∀ j : Fin 24,
      (leechHyperbolicInverse * (generatedTenthAxisLowerRecoveryLatticeBasisData07Matrix).map
        (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ
          monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) =
            monsterCo1GeometryBinaryMaskDecode
              (generatedTenthAxisLowerRecoveryCompactBinaryColumns 7 j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
