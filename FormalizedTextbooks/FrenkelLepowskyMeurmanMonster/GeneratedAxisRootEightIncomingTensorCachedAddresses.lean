/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorCircuitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLabelMatrixFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinQuadraticFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinPauliFast

/-! Exact full monomial address checks for the genuine incoming compact operator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every original inverse column has the complete twelve-bit bound. -/
theorem generatedRootEight_incoming_tensor_inverse_columns_bound : ∀ j : Fin 12,
    generatedRootEightIncomingCompactRightInverseColumns 0 j < 4096 ∧
      generatedRootEightIncomingCompactLeftInverseColumns 0 j < 4096 := by
  decide +kernel

/-- Complete column XOR evaluates the actual original right inverse. -/
theorem generatedRootEight_incoming_tensor_right_inverse_fast (n : Fin 4096) :
    nortonUIntegerLabel ((generatedRootEightIncomingCompactRight 0).symm
      (golayLabelCoefficients n)) =
      ⟨generatedNinthLowerSpinLabelMatrixFast
        (generatedRootEightIncomingCompactRightInverseColumns 0) n.val % 4096,
        Nat.mod_lt _ (by decide)⟩ := by
  exact generatedNinth_lower_spin_label_matrix_fast_code _
    (fun j => (generatedRootEight_incoming_tensor_inverse_columns_bound j).1) n

set_option maxHeartbeats 8000000 in
-- Evaluate the original certified inverse while retaining its full source equivalence.
/-- Complete column XOR retains the original left inverse and actual Pauli translation. -/
theorem generatedRootEight_incoming_tensor_left_inverse_fast (n : Fin 4096) :
    nortonUIntegerLabel ((generatedRootEightIncomingCompactLeft 0).symm
      (golayLabelCoefficients n + spinTranslation (generatedRootEightIncomingCompactPauli 0))) =
      ⟨generatedNinthLowerSpinLabelMatrixFast
        (generatedRootEightIncomingCompactLeftInverseColumns 0)
        (Nat.xor n.val (nortonUIntegerLabel
          (spinTranslation (generatedRootEightIncomingCompactPauli 0))).val % 4096) % 4096,
        Nat.mod_lt _ (by decide)⟩ := by
  change nortonUIntegerLabel (generatedNinthLowerSpinCompactMatrix
    (generatedRootEightIncomingCompactLeftInverseColumns 0) *ᵥ _) = _
  rw [generatedNinth_lower_spin_label_matrix_fast_index _
    (fun j => (generatedRootEight_incoming_tensor_inverse_columns_bound j).2),
    generatedNinth_lower_spin_label_add]

/-- The complete original post address is shared inside its full quadratic phase. -/
def generatedRootEightIncomingTensorCachedAddressCondition (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedRootEightIncomingTensorPreLabel n =
      nortonUIntegerLabel ((generatedRootEightIncomingCompactRight 0).symm t) ∧
    generatedRootEightIncomingTensorPreSign n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactSecondPhaseRows 0))
          t) ∧
    generatedRootEightIncomingTensorPostLabel n = nortonUIntegerLabel
      ((generatedRootEightIncomingCompactLeft 0).symm
        (t + spinTranslation (generatedRootEightIncomingCompactPauli 0))) ∧
    generatedRootEightIncomingTensorPostSign n =
      nortonUIntegerSign (spinPhase (generatedRootEightIncomingCompactPauli 0) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactFirstPhaseRows 0))
            (golayLabelCoefficients (generatedRootEightIncomingTensorPostLabel n)))

/-- The complete post coordinate certificate evaluates exactly the original inverse phase. -/
theorem generatedRootEight_incoming_tensor_address_of_cached (n : Fin 4096)
    (h : generatedRootEightIncomingTensorCachedAddressCondition n) :
    generatedRootEightIncomingTensorAddressCondition n := by
  unfold generatedRootEightIncomingTensorCachedAddressCondition at h
  unfold generatedRootEightIncomingTensorAddressCondition
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  have hp := congrArg golayLabelCoefficients h.2.2.1
  simp only [nortonUIntegerLabel_inverse] at hp
  simpa only [hp] using h.2.2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
