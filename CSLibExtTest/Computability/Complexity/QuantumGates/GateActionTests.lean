/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.GateAction

/-!
# Tests: computational-basis gate actions
-/

@[expose] public section

namespace Cslib.Complexity.Classes.Tests

set_option autoImplicit false

open Cslib.Complexity.Classes Cslib.Complexity.Classes.QuantumGates

#print axioms applyCircuit_toffoliGates
#print axioms applyGate_embeddedGate
#print axioms applyGate_controlledGate

/-- Nonvacuity at `N = 3`, in-order indices: the Toffoli index swaps the
two basis states with both controls set and fixes the other six, and the
five-gate circuit realizes it on basis states. -/
theorem toffoli_three_check :
    toffoliIndex 3 0 1 2 3 = 7 ∧ toffoliIndex 3 0 1 2 7 = 3 ∧
      (∀ s : Fin (2 ^ 3), s ≠ 3 → s ≠ 7 → toffoliIndex 3 0 1 2 s = s) ∧
      applyCircuit 3 (toffoliGates 0 1 2) (Pi.single 3 1) = Pi.single 7 1 ∧
      applyCircuit 3 (toffoliGates 0 1 2) (Pi.single 5 1) = Pi.single 5 1 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · decide
  · rw [applyCircuit_toffoliGates_single]
    · congr 1
    all_goals (first | decide)
  · rw [applyCircuit_toffoliGates_single]
    · congr 1
    all_goals (first | decide)

/-- Nonvacuity at `N = 5` with out-of-order indices `a = 4, b = 0, c = 2`:
`17 = 10001₂` has both controls set, so qubit `2` flips to `21 = 10101₂`;
`16 = 10000₂` has control `b = 0` clear and is fixed. -/
theorem toffoli_five_check :
    toffoliIndex 5 4 0 2 17 = 21 ∧
      applyCircuit 5 (toffoliGates 4 0 2) (Pi.single 17 1) = Pi.single 21 1 ∧
      applyCircuit 5 (toffoliGates 4 0 2) (Pi.single 16 1) = Pi.single 16 1 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [applyCircuit_toffoliGates_single]
    · congr 1
    all_goals (first | decide)
  · rw [applyCircuit_toffoliGates_single]
    · congr 1
    all_goals (first | decide)

/-- Both placement branches of an embedded `X` (`q > p` and `q < p`), and
both CNOT orientations, on basis states at `N = 3`. -/
theorem embedded_and_cnot_check :
    applyGate 3 (embeddedGate xGate 2 0) (Pi.single 0 1) = Pi.single 4 1 ∧
      applyGate 3 (embeddedGate xGate 0 2) (Pi.single 0 1) = Pi.single 1 1 ∧
      applyGate 3 (controlledGate xGate 0 2) (Pi.single 1 1) = Pi.single 5 1 ∧
      applyGate 3 (controlledGate xGate 2 0) (Pi.single 1 1) = Pi.single 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · first | rw [applyGate_embeddedGate_xGate_single]
    · congr 1
    all_goals (first | decide)
  · first | rw [applyGate_embeddedGate_xGate_single]
    · congr 1
    all_goals (first | decide)
  · first | rw [applyGate_cnot_single]
    · congr 1
    all_goals (first | decide)
  · first | rw [applyGate_cnot_single]
    · congr 1
    all_goals (first | decide)

/-- Swap exchanges the outer qubits at `N = 3`, and `Z` phases the
`1` branch: at the basis state `1`, an embedded `Z` at qubit `0` has
amplitude `-1` at `1` and `0` at `0`. -/
theorem swap_and_z_check :
    applyGate 3 (0, 2, swapEntries) (Pi.single 1 1) = Pi.single 4 1 ∧
      applyGate 3 (embeddedGate zGate 0 1) (Pi.single 1 1) 1 = -1 ∧
      applyGate 3 (embeddedGate zGate 0 1) (Pi.single 1 1) 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · funext u
    rw [applyGate_swap (by decide) (by decide)]
    fin_cases u
    · show Pi.single (M := fun _ => ℂ) (1 : Fin (2 ^ 3)) (1 : ℂ)
            (setQBit 3 0 (qBit 2 (0 : Fin (2 ^ 3)).val)
              (setQBit 3 2 (qBit 0 (0 : Fin (2 ^ 3)).val) 0))
          = Pi.single (M := fun _ => ℂ) (4 : Fin (2 ^ 3)) (1 : ℂ) (0 : Fin (2 ^ 3))
      have hidx : setQBit 3 0 (qBit 2 (0 : Fin (2 ^ 3)).val)
          (setQBit 3 2 (qBit 0 (0 : Fin (2 ^ 3)).val) 0)
          = (0 : Fin (2 ^ 3)) := by decide
      have hL : (0 : Fin (2 ^ 3)) ≠ 1 := by decide
      have hR : (0 : Fin (2 ^ 3)) ≠ 4 := by decide
      rw [hidx, Pi.single_eq_of_ne hL _, Pi.single_eq_of_ne hR _]
    · show Pi.single (M := fun _ => ℂ) (1 : Fin (2 ^ 3)) (1 : ℂ)
            (setQBit 3 0 (qBit 2 (1 : Fin (2 ^ 3)).val)
              (setQBit 3 2 (qBit 0 (1 : Fin (2 ^ 3)).val) 1))
          = Pi.single (M := fun _ => ℂ) (4 : Fin (2 ^ 3)) (1 : ℂ) (1 : Fin (2 ^ 3))
      have hidx : setQBit 3 0 (qBit 2 (1 : Fin (2 ^ 3)).val)
          (setQBit 3 2 (qBit 0 (1 : Fin (2 ^ 3)).val) 1)
          = (4 : Fin (2 ^ 3)) := by decide
      have hL : (4 : Fin (2 ^ 3)) ≠ 1 := by decide
      have hR : (1 : Fin (2 ^ 3)) ≠ 4 := by decide
      rw [hidx, Pi.single_eq_of_ne hL _, Pi.single_eq_of_ne hR _]
    · show Pi.single (M := fun _ => ℂ) (1 : Fin (2 ^ 3)) (1 : ℂ)
            (setQBit 3 0 (qBit 2 (2 : Fin (2 ^ 3)).val)
              (setQBit 3 2 (qBit 0 (2 : Fin (2 ^ 3)).val) 2))
          = Pi.single (M := fun _ => ℂ) (4 : Fin (2 ^ 3)) (1 : ℂ) (2 : Fin (2 ^ 3))
      have hidx : setQBit 3 0 (qBit 2 (2 : Fin (2 ^ 3)).val)
          (setQBit 3 2 (qBit 0 (2 : Fin (2 ^ 3)).val) 2)
          = (2 : Fin (2 ^ 3)) := by decide
      have hL : (2 : Fin (2 ^ 3)) ≠ 1 := by decide
      have hR : (2 : Fin (2 ^ 3)) ≠ 4 := by decide
      rw [hidx, Pi.single_eq_of_ne hL _, Pi.single_eq_of_ne hR _]
    · show Pi.single (M := fun _ => ℂ) (1 : Fin (2 ^ 3)) (1 : ℂ)
            (setQBit 3 0 (qBit 2 (3 : Fin (2 ^ 3)).val)
              (setQBit 3 2 (qBit 0 (3 : Fin (2 ^ 3)).val) 3))
          = Pi.single (M := fun _ => ℂ) (4 : Fin (2 ^ 3)) (1 : ℂ) (3 : Fin (2 ^ 3))
      have hidx : setQBit 3 0 (qBit 2 (3 : Fin (2 ^ 3)).val)
          (setQBit 3 2 (qBit 0 (3 : Fin (2 ^ 3)).val) 3)
          = (6 : Fin (2 ^ 3)) := by decide
      have hL : (6 : Fin (2 ^ 3)) ≠ 1 := by decide
      have hR : (3 : Fin (2 ^ 3)) ≠ 4 := by decide
      rw [hidx, Pi.single_eq_of_ne hL _, Pi.single_eq_of_ne hR _]
    · show Pi.single (M := fun _ => ℂ) (1 : Fin (2 ^ 3)) (1 : ℂ)
            (setQBit 3 0 (qBit 2 (4 : Fin (2 ^ 3)).val)
              (setQBit 3 2 (qBit 0 (4 : Fin (2 ^ 3)).val) 4))
          = Pi.single (M := fun _ => ℂ) (4 : Fin (2 ^ 3)) (1 : ℂ) (4 : Fin (2 ^ 3))
      have hidx : setQBit 3 0 (qBit 2 (4 : Fin (2 ^ 3)).val)
          (setQBit 3 2 (qBit 0 (4 : Fin (2 ^ 3)).val) 4)
          = (1 : Fin (2 ^ 3)) := by decide
      rw [hidx, Pi.single_eq_same, Pi.single_eq_same]
    · show Pi.single (M := fun _ => ℂ) (1 : Fin (2 ^ 3)) (1 : ℂ)
            (setQBit 3 0 (qBit 2 (5 : Fin (2 ^ 3)).val)
              (setQBit 3 2 (qBit 0 (5 : Fin (2 ^ 3)).val) 5))
          = Pi.single (M := fun _ => ℂ) (4 : Fin (2 ^ 3)) (1 : ℂ) (5 : Fin (2 ^ 3))
      have hidx : setQBit 3 0 (qBit 2 (5 : Fin (2 ^ 3)).val)
          (setQBit 3 2 (qBit 0 (5 : Fin (2 ^ 3)).val) 5)
          = (5 : Fin (2 ^ 3)) := by decide
      have hL : (5 : Fin (2 ^ 3)) ≠ 1 := by decide
      have hR : (5 : Fin (2 ^ 3)) ≠ 4 := by decide
      rw [hidx, Pi.single_eq_of_ne hL _, Pi.single_eq_of_ne hR _]
    · show Pi.single (M := fun _ => ℂ) (1 : Fin (2 ^ 3)) (1 : ℂ)
            (setQBit 3 0 (qBit 2 (6 : Fin (2 ^ 3)).val)
              (setQBit 3 2 (qBit 0 (6 : Fin (2 ^ 3)).val) 6))
          = Pi.single (M := fun _ => ℂ) (4 : Fin (2 ^ 3)) (1 : ℂ) (6 : Fin (2 ^ 3))
      have hidx : setQBit 3 0 (qBit 2 (6 : Fin (2 ^ 3)).val)
          (setQBit 3 2 (qBit 0 (6 : Fin (2 ^ 3)).val) 6)
          = (3 : Fin (2 ^ 3)) := by decide
      have hL : (3 : Fin (2 ^ 3)) ≠ 1 := by decide
      have hR : (6 : Fin (2 ^ 3)) ≠ 4 := by decide
      rw [hidx, Pi.single_eq_of_ne hL _, Pi.single_eq_of_ne hR _]
    · show Pi.single (M := fun _ => ℂ) (1 : Fin (2 ^ 3)) (1 : ℂ)
            (setQBit 3 0 (qBit 2 (7 : Fin (2 ^ 3)).val)
              (setQBit 3 2 (qBit 0 (7 : Fin (2 ^ 3)).val) 7))
          = Pi.single (M := fun _ => ℂ) (4 : Fin (2 ^ 3)) (1 : ℂ) (7 : Fin (2 ^ 3))
      have hidx : setQBit 3 0 (qBit 2 (7 : Fin (2 ^ 3)).val)
          (setQBit 3 2 (qBit 0 (7 : Fin (2 ^ 3)).val) 7)
          = (7 : Fin (2 ^ 3)) := by decide
      have hL : (7 : Fin (2 ^ 3)) ≠ 1 := by decide
      have hR : (7 : Fin (2 ^ 3)) ≠ 4 := by decide
      rw [hidx, Pi.single_eq_of_ne hL _, Pi.single_eq_of_ne hR _]
  · have h1 : qBit 0 (1 : Fin (2 ^ 3)).val = 1 := by decide
    rw [applyGate_embeddedGate_zGate (by decide) (by decide) (by decide),
      ite_eq_left h1, Pi.single_eq_same, mul_one]
  · have h0 : ¬ qBit 0 (0 : Fin (2 ^ 3)).val = 1 := by decide
    have h01 : (0 : Fin (2 ^ 3)) ≠ 1 := by decide
    rw [applyGate_embeddedGate_zGate (by decide) (by decide) (by decide),
      ite_eq_right h0, Pi.single_eq_of_ne h01 _, mul_zero]
/-- Locality instance with a dirty qubit: gates on qubits `0, 1` cannot
create amplitude where qubit `2` is `1`, starting from a state supported
on qubit `2` equal to `0`. -/
theorem locality_check (s : Fin (2 ^ 3)) (hs : qBit 2 s.val ≠ 0) :
    applyCircuit 3 [embeddedGate xGate 0 1, controlledGate xGate 0 1]
      (Pi.single 3 1) s = 0 := by
  have hwf1 : QGateWellFormed 3 (embeddedGate xGate 0 1) := by
    apply embeddedGate_wellFormed
    all_goals (first | exact xGate_unitary | decide)
  have hwf2 : QGateWellFormed 3 (controlledGate xGate 0 1) := by
    apply controlledGate_wellFormed
    all_goals (first | exact xGate_unitary | decide)
  apply applyCircuit_eq_zero_of_qBit_ne (r := 2) (v := 0)
  all_goals (
    first
      | exact hs
      | (intro g hg; simp at hg; rcases hg with rfl | rfl <;>
          (first | exact hwf1 | exact hwf2 | decide |
            (refine ⟨hwf1, ?_, ?_⟩ <;> decide) | (refine ⟨hwf2, ?_, ?_⟩ <;> decide)))
      | (intro t ht; by_cases h : t = 3 <;>
          (first | (subst h; exact (ht (by decide)).elim) | exact Pi.single_eq_of_ne h 1)))

end Cslib.Complexity.Classes.Tests
