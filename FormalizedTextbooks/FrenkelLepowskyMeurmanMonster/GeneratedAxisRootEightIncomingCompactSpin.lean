/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinCompactData

/-! Actual compact spin factors for the original root-eight words and incoming transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightIncomingCompactLeftColumns : Fin 1 → Fin 12 → ℕ :=
  ![![845, 847, 179, 2227, 2833, 5, 1010, 2088, 1, 16, 256, 1024]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightIncomingCompactLeftInverseColumns : Fin 1 → Fin 12 → ℕ :=
  ![![256, 3, 288, 357, 512, 489, 600, 750, 1024, 1820, 2048, 12]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightIncomingCompactRightColumns : Fin 1 → Fin 12 → ℕ :=
  ![![256, 1792, 3072, 3084, 16, 768, 64, 2567, 128, 800, 1539, 257]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightIncomingCompactRightInverseColumns : Fin 1 → Fin 12 → ℕ :=
  ![![2049, 3074, 1156, 1160, 16, 544, 64, 256, 1, 33, 34, 38]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightIncomingCompactFirstPhaseRows : Fin 1 → Fin 12 → ℕ :=
  ![![1996, 2304, 1600, 1232, 3872, 3392, 3200, 256, 0, 0, 0, 0]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightIncomingCompactSecondPhaseRows : Fin 1 → Fin 12 → ℕ :=
  ![![1280, 1036, 2784, 3040, 3584, 2048, 1280, 3072, 3584, 2048, 2048, 0]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightIncomingCompactBinaryColumns : Fin 1 → Fin 24 → ℕ :=
  ![![2643981, 2755269, 114421, 2486005, 7929856, 1882892, 2054144, 240813, 7931904, 5600012,
    2689736, 3680269, 3277645, 1233743, 5316787, 1190067, 14359313, 2445317, 7660530, 198656,
    8452136, 7884805, 6413135, 6225922]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightIncomingCompactUnitPhases : Fin 1 → Fin 24 → ℕ :=
  ![![0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]]

/-- The number of original individual Fourier factors in each actual compact model. -/
def generatedRootEightIncomingCompactHadamardRank : Fin 1 → Fin 13 :=
  ![8]

/-- The actual full Pauli coordinates, with a chosen zero scalar representative. -/
def generatedRootEightIncomingCompactPauliLabels : Fin 1 → Fin 4096 × Fin 4096 × ZMod 2 :=
  ![(155, 2954, 0)]

set_option maxHeartbeats 8000000 in
-- Evaluate the two-sided binary matrix products for both original monomial factors.
/-- Every compact monomial factor has its actual two-sided binary inverse. -/
theorem generatedRootEight_incoming_compact_matrix_inverse : ∀ i : Fin 1,
    (generatedNinthLowerSpinCompactMatrix (generatedRootEightIncomingCompactLeftInverseColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedRootEightIncomingCompactLeftColumns i) = 1 ∧
      generatedNinthLowerSpinCompactMatrix (generatedRootEightIncomingCompactLeftColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedRootEightIncomingCompactLeftInverseColumns
    i) = 1) ∧
    (generatedNinthLowerSpinCompactMatrix (generatedRootEightIncomingCompactRightInverseColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedRootEightIncomingCompactRightColumns i) = 1 ∧
      generatedNinthLowerSpinCompactMatrix (generatedRootEightIncomingCompactRightColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedRootEightIncomingCompactRightInverseColumns
    i) = 1) := by
  decide +kernel

/-- The left original compact monomial is a genuine binary spin equivalence. -/
def generatedRootEightIncomingCompactLeft (i : Fin 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedNinthLowerSpinCompactEquiv (generatedRootEightIncomingCompactLeftColumns i)
    (generatedRootEightIncomingCompactLeftInverseColumns i)
    (generatedRootEight_incoming_compact_matrix_inverse i).1.1
    (generatedRootEight_incoming_compact_matrix_inverse i).1.2

/-- The right original compact monomial is a genuine binary spin equivalence. -/
def generatedRootEightIncomingCompactRight (i : Fin 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedNinthLowerSpinCompactEquiv (generatedRootEightIncomingCompactRightColumns i)
    (generatedRootEightIncomingCompactRightInverseColumns i)
    (generatedRootEight_incoming_compact_matrix_inverse i).2.1
    (generatedRootEight_incoming_compact_matrix_inverse i).2.2

/-- The full Pauli factor belongs to the actual original extraspecial group. -/
def generatedRootEightIncomingCompactPauli (i : Fin 1) : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients (generatedRootEightIncomingCompactPauliLabels i).1)
    (golayLabelCoefficients (generatedRootEightIncomingCompactPauliLabels i).2.1)),
    ofAdd (generatedRootEightIncomingCompactPauliLabels i).2.2⟩

/-- The prescribed original coordinates receive the individual Fourier factors. -/
def generatedRootEightIncomingCompactHadamardWord (i : Fin 1) : List (Fin 12) :=
  (List.finRange 12).filter (fun k => k.val < (generatedRootEightIncomingCompactHadamardRank i).val)

/-- An actual orthogonal spin normalizer built from original monomials, phases and Fourier maps. -/
def generatedRootEightIncomingCompactSpin (i : Fin 1) : SpinHolomorph :=
  spinHolomorphIncl (generatedRootEightIncomingCompactPauli i) *
    monsterMonomialPermutationHolomorph (generatedRootEightIncomingCompactLeft i) *
    monsterMonomialDiagonalHolomorph
      (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactFirstPhaseRows i)) *
    ((generatedRootEightIncomingCompactHadamardWord i).map generatedNinthLowerSpinHadamard).prod *
    monsterMonomialDiagonalHolomorph
      (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactSecondPhaseRows i)) *
    monsterMonomialPermutationHolomorph (generatedRootEightIncomingCompactRight i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
