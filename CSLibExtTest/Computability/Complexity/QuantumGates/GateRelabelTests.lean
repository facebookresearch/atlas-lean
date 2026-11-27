/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.GateRelabel

/-!
# Tests: Gate relabeling at the encoding level
-/

@[expose] public section

open Cslib.Complexity.Classes
namespace CslibTest.Complexity.Classes.QuantumGates

set_option autoImplicit false

open Cslib.Complexity.Classes.QuantumGates

#print axioms qGateWellFormed_relabelGate
#print axioms relabelGate_ctrlLow

/-- Double conjugation is the identity on exporter outputs. -/
private theorem swapConjEntries_involutive_entriesOf
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat) :
    swapConjEntries (swapConjEntries (entriesOf M)) = entriesOf M := by
  have hsub : ((M.submatrix Prod.swap Prod.swap).submatrix Prod.swap Prod.swap) = M := by
    apply Matrix.ext
    intro p q
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    rfl
  rw [swapConjEntries_entriesOf, swapConjEntries_entriesOf, hsub]

open Cslib.Complexity.Classes in
/-- Relabeling is an involution on a concrete entry list. -/
theorem swapConjEntries_involutive_cnotLow :
    swapConjEntries (swapConjEntries cnotLowEntries) = cnotLowEntries := by
  unfold cnotLowEntries
  exact swapConjEntries_involutive_entriesOf _

/-- Conjugating the low CNOT entries gives the high CNOT entries. -/
theorem swapConjEntries_cnotLow_eq_cnotHigh :
    swapConjEntries cnotLowEntries = cnotHighEntries := by
  unfold cnotLowEntries cnotHighEntries
  rw [swapConjEntries_entriesOf, ctrlLow_submatrix_swap]

/-- On three qubits, reversing the wires sends the low CNOT gate to the high one. -/
theorem relabelGate_rev_cnotLow :
    relabelGate (fun n => 2 - n) (0, 2, cnotLowEntries) = (0, 2, cnotHighEntries) := by
  have hneg : ¬ (2 - 0 : ℕ) < 2 - 2 := by norm_num
  have h1 : (2 - 2 : ℕ) = 0 := rfl
  have h2 : (2 - 0 : ℕ) = 2 := rfl
  simp [relabelGate, hneg, swapConjEntries_cnotLow_eq_cnotHigh, h1, h2]

/-- The reversed CNOT gate stays well-formed on three qubits. -/
theorem relabelGate_rev_cnotLow_wellFormed
    (hg : QGateWellFormed 3 (0, 2, cnotLowEntries)) :
    QGateWellFormed 3 (relabelGate (fun n => 2 - n) (0, 2, cnotLowEntries)) := by
  have hne : (fun n => 2 - n) 0 ≠ (fun n => 2 - n) 2 := by norm_num
  have h1 : (fun n => 2 - n) 0 < 3 := by norm_num
  have h2 : (fun n => 2 - n) 2 < 3 := by norm_num
  exact qGateWellFormed_relabelGate hg hne h1 h2

/-- An order-preserving shift keeps the entry list. -/
theorem relabelGate_shift_cnotLow :
    relabelGate (· + 1) (0, 1, cnotLowEntries) = (1, 2, cnotLowEntries) := by
  have hpos : (0 + 1 : ℕ) < 1 + 1 := by norm_num
  have h1 : (0 + 1 : ℕ) = 1 := rfl
  have h2 : (1 + 1 : ℕ) = 2 := rfl
  simp [relabelGate, hpos, h1, h2]

/-- The shifted CNOT gate stays well-formed. -/
theorem relabelGate_shift_cnotLow_wellFormed
    (hg : QGateWellFormed 2 (0, 1, cnotLowEntries)) :
    QGateWellFormed 3 (relabelGate (· + 1) (0, 1, cnotLowEntries)) := by
  have hne : (0 + 1 : ℕ) ≠ 1 + 1 := by norm_num
  have h1 : (0 + 1 : ℕ) < 3 := by norm_num
  have h2 : (1 + 1 : ℕ) < 3 := by norm_num
  exact qGateWellFormed_relabelGate hg hne h1 h2

/-- Relabeling is an involution on a second concrete entry list. -/
theorem swapConjEntries_involutive_cnotHigh :
    swapConjEntries (swapConjEntries cnotHighEntries) = cnotHighEntries := by
  unfold cnotHighEntries
  exact swapConjEntries_involutive_entriesOf _

end CslibTest.Complexity.Classes.QuantumGates
