/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinCompactMatrixCertificates

/-! Genuine compact spin factors from previously certified whole binary inverse matrices. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- An exact invertible binary matrix gives an actual spin-coordinate linear equivalence. -/
def generatedTwelfthIncomingSpinCompactEquiv (a b : Fin 12 → ℕ)
    (hleft : generatedTwelfthIncomingSpinCompactMatrix b *
      generatedTwelfthIncomingSpinCompactMatrix a = 1)
    (hright : generatedTwelfthIncomingSpinCompactMatrix a *
      generatedTwelfthIncomingSpinCompactMatrix b = 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun t := generatedTwelfthIncomingSpinCompactMatrix a *ᵥ t
  invFun t := generatedTwelfthIncomingSpinCompactMatrix b *ᵥ t
  left_inv t := by
    change generatedTwelfthIncomingSpinCompactMatrix b *ᵥ
      (generatedTwelfthIncomingSpinCompactMatrix a *ᵥ t) = t
    rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  right_inv t := by
    change generatedTwelfthIncomingSpinCompactMatrix a *ᵥ
      (generatedTwelfthIncomingSpinCompactMatrix b *ᵥ t) = t
    rw [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
  map_add' _ _ := Matrix.mulVec_add _ _ _
  map_smul' _ _ := Matrix.mulVec_smul _ _ _

/-- The exact compact left binary monomial is an actual spin-coordinate equivalence. -/
def generatedTwelfthIncomingSpinCompactLeft (i : Fin 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedTwelfthIncomingSpinCompactEquiv (generatedTwelfthIncomingSpinCompactLeftColumns i)
    (generatedTwelfthIncomingSpinCompactLeftInverseColumns i)
    (generatedTwelfth_incoming_spin_compact_matrix_inverse i).1.1
    (generatedTwelfth_incoming_spin_compact_matrix_inverse i).1.2

/-- The exact compact right binary monomial is an actual spin-coordinate equivalence. -/
def generatedTwelfthIncomingSpinCompactRight (i : Fin 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedTwelfthIncomingSpinCompactEquiv (generatedTwelfthIncomingSpinCompactRightColumns i)
    (generatedTwelfthIncomingSpinCompactRightInverseColumns i)
    (generatedTwelfth_incoming_spin_compact_matrix_inverse i).2.1
    (generatedTwelfth_incoming_spin_compact_matrix_inverse i).2.2

/-- The exact compact source Pauli is an element of the original extraspecial group. -/
def generatedTwelfthIncomingSpinCompactPauli (i : Fin 1) : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients (generatedTwelfthIncomingSpinCompactPauliLabels i).1)
    (golayLabelCoefficients (generatedTwelfthIncomingSpinCompactPauliLabels i).2.1)),
    ofAdd (generatedTwelfthIncomingSpinCompactPauliLabels i).2.2⟩

/-- Individual Fourier factors use precisely the first prescribed original coordinates. -/
def generatedTwelfthIncomingSpinCompactHadamardWord (i : Fin 1) : List (Fin 12) :=
  (List.finRange 12).filter (fun k => k.val < (generatedTwelfthIncomingSpinCompactHadamardRank i).val)

/-- Every compact model is a product of genuine orthogonal spin normalizer elements. -/
def generatedTwelfthIncomingSpinCompact (i : Fin 1) : SpinHolomorph :=
  spinHolomorphIncl (generatedTwelfthIncomingSpinCompactPauli i) *
    monsterMonomialPermutationHolomorph (generatedTwelfthIncomingSpinCompactLeft i) *
    monsterMonomialDiagonalHolomorph
      (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactFirstPhaseRows i)) *
    ((generatedTwelfthIncomingSpinCompactHadamardWord i).map generatedNinthLowerSpinHadamard).prod *
    monsterMonomialDiagonalHolomorph
      (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactSecondPhaseRows i)) *
    monsterMonomialPermutationHolomorph (generatedTwelfthIncomingSpinCompactRight i)


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
