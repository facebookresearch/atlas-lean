/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixActionGeneric

/-! Complete actual integral lattice-basis matrices for candidate5. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData05Matrix : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![0, -2, 1, 1, 1, 0, 0, 1, 1, 2, -1, 3, -1, 1, 1, 0, -1, 10, -6, -1, -6, -1, -3, -5],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 2, 1, 2, 1, 1, 1],
    ![0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 1, 0, 1, 1, 0, 1],
    ![1, 1, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, 1, 0, 0, 0, 0, -3, 1, -1, 1, 0, 0, 1],
    ![0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -2, 1, 0, 1, 0, 1, 1],
    ![-1, 0, -1, -1, -1, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0, 0, -2, 0, 0, 1, 0, 1, 0],
    ![-1, 0, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0, 0, -1, 0, 0, -2, 1, 0, 1, 0, 1, 1],
    ![0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, -2, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 1, 0, 0, 0, 0, -2, 1, 0, 2, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, 0, -1, 0, 0, 1, -2, 2, 1, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0, -1, -1, 0, 1, -1, 0, -1, 0, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, 0, 1]
  ]

/-- Every original integer lattice-basis coordinate. -/
def generatedTenthAxisLowerRecoveryLatticeBasisData05Inverse : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![0, -2, 1, 1, 1, 0, 0, 1, 1, 2, -1, 3, -1, 1, 1, 0, -1, 10, -6, -1, -6, -1, -3, -5],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 2, 1, 2, 1, 1, 1],
    ![0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 1, 0, 1, 1, 0, 1],
    ![1, 1, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, 1, 0, 0, 0, 0, -3, 1, -1, 1, 0, 0, 1],
    ![0, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -2, 1, 0, 1, 0, 1, 1],
    ![-1, 0, -1, -1, -1, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0, 0, -2, 0, 0, 1, 0, 1, 0],
    ![-1, 0, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0, 0, -1, 0, 0, -2, 1, 0, 1, 0, 1, 1],
    ![0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, -2, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 1, 0, 0, 0, 0, -2, 1, 0, 2, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, 0, -1, 0, 0, 1, -2, 2, 1, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0, -1, -1, 0, 1, -1, 0, -1, 0, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, 0, 1]
  ]

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- Whole physical numerator and true denominator act on the complete actual integral basis. -/
theorem generatedTenth_axis_lower_recovery_lattice_basis_05 :
    generatedTenthAxisLowerRecoveryCompactSpatialNumerator 5 * leechBasisMatrix =
      (generatedTenthAxisLowerRecoveryCompactSpatialDenominator 5 : ℤ) •
        (leechBasisMatrix * generatedTenthAxisLowerRecoveryLatticeBasisData05Matrix) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Verify the complete finite lattice certificate at this scoped heartbeat limit.
/-- All24 original hyperbolic binary columns agree with the actual integral basis action. -/
theorem generatedTenth_axis_lower_recovery_lattice_binary_05 :
    ∀ j : Fin 24,
      (leechHyperbolicInverse * (generatedTenthAxisLowerRecoveryLatticeBasisData05Matrix).map
        (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ
          monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) =
            monsterCo1GeometryBinaryMaskDecode
              (generatedTenthAxisLowerRecoveryCompactBinaryColumns 5 j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
