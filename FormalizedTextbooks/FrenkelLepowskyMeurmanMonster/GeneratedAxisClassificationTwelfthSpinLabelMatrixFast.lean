/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinLabelXor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Exact source labels of every genuine compact monomial are computed by whole column XOR.
The actual twelve-coordinate linear maps and their certified inverses are retained. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Whole original binary columns, selected in their exact twelve-coordinate source order. -/
def generatedTwelfthSpinLabelMatrixFast (cols : Fin 12 → ℕ) (v : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun j : Fin 12 =>
    if v.testBit j.val then cols j else 0))

private theorem sum_bound (xs : List ℕ) (h : ∀ x ∈ xs, x < 4096) :
    monsterCo1GeometryBinaryMaskSum xs < 4096 := by
  induction xs with
  | nil => decide
  | cons a xs ih =>
    unfold monsterCo1GeometryBinaryMaskSum
    exact Nat.xor_lt_two_pow (n := 12) (h a (by simp))
      (ih (fun x hx => h x (by simp [hx])))

/-- Bounded complete original columns produce a bounded complete original spin label. -/
theorem generatedTwelfth_spin_label_matrix_fast_bound (cols : Fin 12 → ℕ)
    (hc : ∀ j, cols j < 4096) (v : ℕ) :
    generatedTwelfthSpinLabelMatrixFast cols v < 4096 := by
  apply sum_bound
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  split
  · exact hc j
  · decide

/-- The selected full-column XOR decodes to the entire original binary matrix action. -/
theorem generatedTwelfth_spin_label_matrix_fast_decode (cols : Fin 12 → ℕ) (n : Fin 4096) :
    monsterCo1GeometryBinaryMaskDecode (n := 12)
        (generatedTwelfthSpinLabelMatrixFast cols n.val) =
      generatedTwelfthSpinCompactMatrix cols *ᵥ golayLabelCoefficients n := by
  unfold generatedTwelfthSpinLabelMatrixFast
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  ext i
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, generatedTwelfthSpinCompactMatrix]
  apply Finset.sum_congr rfl
  intro j _
  cases h : n.val.testBit j.val <;>
    simp [monsterCo1GeometryBinaryMaskDecode, golayLabelCoefficients, golayBooleanCast, h]

/-- Every actual integer source label follows from complete column XOR semantics. -/
theorem generatedTwelfth_spin_label_matrix_fast_code (cols : Fin 12 → ℕ)
    (hc : ∀ j, cols j < 4096) (n : Fin 4096) :
    nortonUIntegerLabel (generatedTwelfthSpinCompactMatrix cols *ᵥ golayLabelCoefficients n) =
      ⟨generatedTwelfthSpinLabelMatrixFast cols n.val % 4096, Nat.mod_lt _ (by decide)⟩ := by
  apply golayLabelCoefficients_injective
  rw [nortonUIntegerLabel_inverse]
  have hb := generatedTwelfth_spin_label_matrix_fast_bound cols hc n.val
  simp only [Nat.mod_eq_of_lt hb, generatedTwelfth_spin_label_decode]
  exact (generatedTwelfth_spin_label_matrix_fast_decode cols n).symm

/-- Complete column XOR semantics applies to every genuine spin index. -/
theorem generatedTwelfth_spin_label_matrix_fast_index (cols : Fin 12 → ℕ)
    (hc : ∀ j, cols j < 4096) (t : SpinIndex) :
    nortonUIntegerLabel (generatedTwelfthSpinCompactMatrix cols *ᵥ t) =
      ⟨generatedTwelfthSpinLabelMatrixFast cols (nortonUIntegerLabel t).val % 4096,
        Nat.mod_lt _ (by decide)⟩ := by
  simpa only [nortonUIntegerLabel_inverse] using
    generatedTwelfth_spin_label_matrix_fast_code cols hc (nortonUIntegerLabel t)

/-- The actual source label of addition by any genuine spin translation is its complete XOR. -/
theorem generatedTwelfth_spin_label_add (n : Fin 4096) (a : SpinIndex) :
    nortonUIntegerLabel (golayLabelCoefficients n + a) =
      ⟨Nat.xor n.val (nortonUIntegerLabel a).val % 4096, Nat.mod_lt _ (by decide)⟩ := by
  have hx : Nat.xor n.val (nortonUIntegerLabel a).val < 4096 :=
    Nat.xor_lt_two_pow (n := 12) n.isLt (nortonUIntegerLabel a).isLt
  apply golayLabelCoefficients_injective
  rw [nortonUIntegerLabel_inverse]
  simp_rw [generatedTwelfth_spin_label_decode]
  simp only [Nat.mod_eq_of_lt hx, monsterCo1GeometryBinaryMaskDecode_xor]
  rw [← generatedTwelfth_spin_label_decode (nortonUIntegerLabel a), nortonUIntegerLabel_inverse]

/-- All original compact inverse columns have their complete twelve-bit bounds. -/
theorem generatedTwelfth_spin_label_inverse_columns_bound : ∀ (g : Fin 12) (j : Fin 12),
    generatedTwelfthSpinCompactRightInverseColumns g j < 4096 ∧
      generatedTwelfthSpinCompactLeftInverseColumns g j < 4096 := by
  decide +kernel

/-- Every complete original pre-boundary address uses its actual compact inverse columns. -/
theorem generatedTwelfth_spin_label_right_inverse_fast (g : Fin 12) (n : Fin 4096) :
    nortonUIntegerLabel ((generatedTwelfthSpinCompactRight g).symm (golayLabelCoefficients n)) =
      ⟨generatedTwelfthSpinLabelMatrixFast (generatedTwelfthSpinCompactRightInverseColumns g)
        n.val % 4096, Nat.mod_lt _ (by decide)⟩ := by
  exact generatedTwelfth_spin_label_matrix_fast_code _
    (fun j => (generatedTwelfth_spin_label_inverse_columns_bound g j).1) n

set_option maxHeartbeats 8000000 in
-- Retain the actual complete source equivalence while evaluating its certified inverse.
/-- Every complete post-boundary address retains its actual inverse and full Pauli translation. -/
theorem generatedTwelfth_spin_label_left_inverse_fast (g : Fin 12) (n : Fin 4096) :
    nortonUIntegerLabel ((generatedTwelfthSpinCompactLeft g).symm
      (golayLabelCoefficients n + spinTranslation (generatedTwelfthSpinCompactPauli g))) =
      ⟨generatedTwelfthSpinLabelMatrixFast (generatedTwelfthSpinCompactLeftInverseColumns g)
        (Nat.xor n.val (nortonUIntegerLabel
          (spinTranslation (generatedTwelfthSpinCompactPauli g))).val % 4096) % 4096,
        Nat.mod_lt _ (by decide)⟩ := by
  change nortonUIntegerLabel (generatedTwelfthSpinCompactMatrix
    (generatedTwelfthSpinCompactLeftInverseColumns g) *ᵥ _) = _
  rw [generatedTwelfth_spin_label_matrix_fast_index _
    (fun j => (generatedTwelfth_spin_label_inverse_columns_bound g j).2),
    generatedTwelfth_spin_label_add]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
