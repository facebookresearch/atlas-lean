/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinHadamard

/-! Exact compact integer data and two-sided binary matrix inverse certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthIncomingSpinCompactLeftColumns : Fin 1 → Fin 12 → ℕ :=
  ![![880, 222, 2231, 14, 794, 99, 218, 1309, 1, 16, 32, 256]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthIncomingSpinCompactLeftInverseColumns : Fin 1 → Fin 12 → ℕ :=
  ![![256, 379, 66, 305, 512, 1024, 1115, 1617, 2048, 2650, 2803, 108]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthIncomingSpinCompactRightColumns : Fin 1 → Fin 12 → ℕ :=
  ![![2304, 3584, 3072, 1293, 3602, 256, 2305, 3140, 1795, 3076, 1571, 128]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthIncomingSpinCompactRightInverseColumns : Fin 1 → Fin 12 → ℕ :=
  ![![65, 322, 516, 584, 336, 1312, 640, 2048, 32, 6, 37, 33]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthIncomingSpinCompactFirstPhaseRows : Fin 1 → Fin 12 → ℕ :=
  ![![1654, 1792, 1296, 1936, 1952, 1536, 1152, 3840, 0, 0, 0, 0]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthIncomingSpinCompactSecondPhaseRows : Fin 1 → Fin 12 → ℕ :=
  ![![3584, 2176, 2160, 2416, 3680, 2624, 128, 3072, 3584, 3072, 0, 0]]

/-- Number of individual normalized Fourier factors in each compact source model. -/
def generatedTwelfthIncomingSpinCompactHadamardRank : Fin 1 → Fin 13 :=
  ![8]

/-- Full Pauli coordinates of the compact model, including its exact scalar sign. -/
def generatedTwelfthIncomingSpinCompactPauliLabels : Fin 1 → Fin 4096 × Fin 4096 × ZMod 2 :=
  ![(3262, 2795, 0)]

/-- Decode an exact compact coefficient column in the original binary spin basis. -/
def generatedTwelfthIncomingSpinCompactMatrix (a : Fin 12 → ℕ) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => golayBooleanCast ((a j).testBit i.val)

/-- Decode an exact upper-triangular quadratic coefficient matrix. -/
def generatedTwelfthIncomingSpinCompactPhase (a : Fin 12 → ℕ) : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => golayBooleanCast ((a i).testBit j.val)

set_option maxHeartbeats 8000000 in
-- Both two-sided products of each proposed monomial inverse use the literal binary columns.
/-- All compact monomial matrices retain their actual two-sided binary inverses. -/
theorem generatedTwelfth_incoming_spin_compact_matrix_inverse : ∀ i : Fin 1,
    (generatedTwelfthIncomingSpinCompactMatrix (generatedTwelfthIncomingSpinCompactLeftInverseColumns i) *
        generatedTwelfthIncomingSpinCompactMatrix (generatedTwelfthIncomingSpinCompactLeftColumns i) = 1 ∧
      generatedTwelfthIncomingSpinCompactMatrix (generatedTwelfthIncomingSpinCompactLeftColumns i) *
        generatedTwelfthIncomingSpinCompactMatrix (generatedTwelfthIncomingSpinCompactLeftInverseColumns i) =
          1) ∧
    (generatedTwelfthIncomingSpinCompactMatrix (generatedTwelfthIncomingSpinCompactRightInverseColumns i) *
        generatedTwelfthIncomingSpinCompactMatrix (generatedTwelfthIncomingSpinCompactRightColumns i) = 1 ∧
      generatedTwelfthIncomingSpinCompactMatrix (generatedTwelfthIncomingSpinCompactRightColumns i) *
        generatedTwelfthIncomingSpinCompactMatrix (generatedTwelfthIncomingSpinCompactRightInverseColumns i) =
          1) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
