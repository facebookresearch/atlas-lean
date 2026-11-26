/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.CircuitMatrix
public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates

/-!
# Tests: circuit matrices

Concrete checks for the circuit-matrix API: the `qubitSplit` register layout and
its agreement with `tensorProd`, the collapse of a tensor factor on zero qubits,
the matrices of the empty and of a two-gate circuit, and the requirement of
`QGateWellFormed` that a gate's first qubit index be below its second.
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates.CircuitMatrixTests

set_option autoImplicit false

open Cslib.Complexity.Classes

/-- The `qubitSplit` layout sends `(1, 0)` to index `1`. -/
theorem qubitSplit_low_one_val : (qubitSplit 1 1 (1, 0)).val = 1 := by decide

/-- The `qubitSplit` layout sends `(0, 1)` to index `2`. -/
theorem qubitSplit_high_one_val : (qubitSplit 1 1 (0, 1)).val = 2 := by decide

/-- `qubitSplit` matches `tensorProd` with a one-qubit second register: at the pair
`(0, 1)` the first factor is read at `0` and the second at `1`. -/
theorem tensorProd_qubitSplit_zero_one (φ χ : Fin (2 ^ 1) → ℂ) :
    tensorProd φ χ (qubitSplit 1 1 (0, 1)) = φ 0 * χ 1 :=
  tensorProd_qubitSplit φ χ 0 1

/-- With no ancilla qubits the BQP initial state is the basis state of the input:
the tensor factor on zero qubits collapses (`tensorProd_zeroState_zero`). -/
theorem bqpInitState_zero (x : List Bool) : bqpInitState x 0 = basisState x :=
  tensorProd_zeroState_zero (basisState x)

/-- The empty circuit has the identity matrix. -/
theorem circuitMatrix_nil : circuitMatrix 2 [] = 1 := rfl

/-- The matrix of a two-gate list has the first gate on the right. -/
theorem circuitMatrix_pair (N : ℕ) (g₁ g₂ : QGate) :
    circuitMatrix N [g₁, g₂] = gateMatrix N g₂ * gateMatrix N g₁ := by
  simp [circuitMatrix]

/-- A gate whose first qubit index is not below its second is not well formed:
the X gate on the low qubit, given the qubits `(1, 0)`, fails the requirement
`i < j` of `QGateWellFormed`. -/
theorem xLow_reversed_qubits_not_wellFormed :
    ¬ QGateWellFormed 2 (1, 0, QuantumGates.xLowEntries) :=
  fun h => absurd h.1 (by decide)

#print axioms qubitSplit_apply_val
#print axioms tensorProd_qubitSplit
#print axioms applyCircuit_eq_circuitMatrix_mulVec
#print axioms circuitMatrix_mem_unitaryGroup
#print axioms tensorProd_zeroState_zero
#print axioms qubitSplit_low_one_val
#print axioms qubitSplit_high_one_val
#print axioms tensorProd_qubitSplit_zero_one
#print axioms bqpInitState_zero
#print axioms circuitMatrix_nil
#print axioms circuitMatrix_pair
#print axioms xLow_reversed_qubits_not_wellFormed

end Cslib.Complexity.Classes.QuantumGates.CircuitMatrixTests
