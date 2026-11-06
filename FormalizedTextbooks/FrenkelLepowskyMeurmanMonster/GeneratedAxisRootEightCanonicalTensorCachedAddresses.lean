/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCircuitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLabelMatrixFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinQuadraticFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinPauliFast

/-! Exact full monomial address checks for the genuine canonical compact operator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every original inverse column has the complete twelve-bit bound. -/
theorem generatedRootEight_canonical_tensor_inverse_columns_bound : ∀ j : Fin 12,
    generatedRootEightCompactRightInverseColumns 12 j < 4096 ∧
      generatedRootEightCompactLeftInverseColumns 12 j < 4096 := by
  decide +kernel

/-- Complete column XOR evaluates the actual original right inverse. -/
theorem generatedRootEight_canonical_tensor_right_inverse_fast (n : Fin 4096) :
    nortonUIntegerLabel ((generatedRootEightCompactRight 12).symm
      (golayLabelCoefficients n)) =
      ⟨generatedNinthLowerSpinLabelMatrixFast
        (generatedRootEightCompactRightInverseColumns 12) n.val % 4096,
        Nat.mod_lt _ (by decide)⟩ := by
  exact generatedNinth_lower_spin_label_matrix_fast_code _
    (fun j => (generatedRootEight_canonical_tensor_inverse_columns_bound j).1) n

set_option maxHeartbeats 8000000 in
-- Evaluate the original certified inverse while retaining its full source equivalence.
/-- Complete column XOR retains the original left inverse and actual Pauli translation. -/
theorem generatedRootEight_canonical_tensor_left_inverse_fast (n : Fin 4096) :
    nortonUIntegerLabel ((generatedRootEightCompactLeft 12).symm
      (golayLabelCoefficients n + spinTranslation (generatedRootEightCompactPauli 12))) =
      ⟨generatedNinthLowerSpinLabelMatrixFast
        (generatedRootEightCompactLeftInverseColumns 12)
        (Nat.xor n.val (nortonUIntegerLabel
          (spinTranslation (generatedRootEightCompactPauli 12))).val % 4096) % 4096,
        Nat.mod_lt _ (by decide)⟩ := by
  change nortonUIntegerLabel (generatedNinthLowerSpinCompactMatrix
    (generatedRootEightCompactLeftInverseColumns 12) *ᵥ _) = _
  rw [generatedNinth_lower_spin_label_matrix_fast_index _
    (fun j => (generatedRootEight_canonical_tensor_inverse_columns_bound j).2),
    generatedNinth_lower_spin_label_add]

/-- The complete original post address is shared inside its full quadratic phase. -/
def generatedRootEightCanonicalTensorCachedAddressCondition (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedRootEightCanonicalTensorPreLabel n =
      nortonUIntegerLabel ((generatedRootEightCompactRight 12).symm t) ∧
    generatedRootEightCanonicalTensorPreSign n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 12))
          t) ∧
    generatedRootEightCanonicalTensorPostLabel n = nortonUIntegerLabel
      ((generatedRootEightCompactLeft 12).symm
        (t + spinTranslation (generatedRootEightCompactPauli 12))) ∧
    generatedRootEightCanonicalTensorPostSign n =
      nortonUIntegerSign (spinPhase (generatedRootEightCompactPauli 12) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 12))
            (golayLabelCoefficients (generatedRootEightCanonicalTensorPostLabel n)))

/-- The complete post coordinate certificate evaluates exactly the original inverse phase. -/
theorem generatedRootEight_canonical_tensor_address_of_cached (n : Fin 4096)
    (h : generatedRootEightCanonicalTensorCachedAddressCondition n) :
    generatedRootEightCanonicalTensorAddressCondition n := by
  unfold generatedRootEightCanonicalTensorCachedAddressCondition at h
  unfold generatedRootEightCanonicalTensorAddressCondition
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  have hp := congrArg golayLabelCoefficients h.2.2.1
  simp only [nortonUIntegerLabel_inverse] at hp
  simpa only [hp] using h.2.2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
