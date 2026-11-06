/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinCompactMatrixCertificates

/-! Genuine compact spin factors from previously certified whole binary inverse matrices. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- An exact invertible binary matrix gives an actual spin-coordinate linear equivalence. -/
def generatedNinthLowerSpinCompactEquiv (a b : Fin 12 → ℕ)
    (hleft : generatedNinthLowerSpinCompactMatrix b *
      generatedNinthLowerSpinCompactMatrix a = 1)
    (hright : generatedNinthLowerSpinCompactMatrix a *
      generatedNinthLowerSpinCompactMatrix b = 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun t := generatedNinthLowerSpinCompactMatrix a *ᵥ t
  invFun t := generatedNinthLowerSpinCompactMatrix b *ᵥ t
  left_inv t := by
    change generatedNinthLowerSpinCompactMatrix b *ᵥ
      (generatedNinthLowerSpinCompactMatrix a *ᵥ t) = t
    rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  right_inv t := by
    change generatedNinthLowerSpinCompactMatrix a *ᵥ
      (generatedNinthLowerSpinCompactMatrix b *ᵥ t) = t
    rw [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
  map_add' _ _ := Matrix.mulVec_add _ _ _
  map_smul' _ _ := Matrix.mulVec_smul _ _ _

/-- The exact compact left binary monomial is an actual spin-coordinate equivalence. -/
def generatedNinthLowerSpinCompactLeft (i : Fin 11) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedNinthLowerSpinCompactEquiv (generatedNinthLowerSpinCompactLeftColumns i)
    (generatedNinthLowerSpinCompactLeftInverseColumns i)
    (generatedNinth_lower_spin_compact_matrix_inverse i).1.1
    (generatedNinth_lower_spin_compact_matrix_inverse i).1.2

/-- The exact compact right binary monomial is an actual spin-coordinate equivalence. -/
def generatedNinthLowerSpinCompactRight (i : Fin 11) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedNinthLowerSpinCompactEquiv (generatedNinthLowerSpinCompactRightColumns i)
    (generatedNinthLowerSpinCompactRightInverseColumns i)
    (generatedNinth_lower_spin_compact_matrix_inverse i).2.1
    (generatedNinth_lower_spin_compact_matrix_inverse i).2.2

/-- The exact compact source Pauli is an element of the original extraspecial group. -/
def generatedNinthLowerSpinCompactPauli (i : Fin 11) : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients (generatedNinthLowerSpinCompactPauliLabels i).1)
    (golayLabelCoefficients (generatedNinthLowerSpinCompactPauliLabels i).2.1)),
    ofAdd (generatedNinthLowerSpinCompactPauliLabels i).2.2⟩

/-- Individual Fourier factors use precisely the first prescribed original coordinates. -/
def generatedNinthLowerSpinCompactHadamardWord (i : Fin 11) : List (Fin 12) :=
  (List.finRange 12).filter (fun k => k.val < (generatedNinthLowerSpinCompactHadamardRank i).val)

/-- Every compact model is a product of genuine orthogonal spin normalizer elements. -/
def generatedNinthLowerSpinCompact (i : Fin 11) : SpinHolomorph :=
  spinHolomorphIncl (generatedNinthLowerSpinCompactPauli i) *
    monsterMonomialPermutationHolomorph (generatedNinthLowerSpinCompactLeft i) *
    monsterMonomialDiagonalHolomorph
      (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactFirstPhaseRows i)) *
    ((generatedNinthLowerSpinCompactHadamardWord i).map generatedNinthLowerSpinHadamard).prod *
    monsterMonomialDiagonalHolomorph
      (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactSecondPhaseRows i)) *
    monsterMonomialPermutationHolomorph (generatedNinthLowerSpinCompactRight i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
