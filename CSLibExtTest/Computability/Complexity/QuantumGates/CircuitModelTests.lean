/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.CircuitModel
public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates

/-!
# Tests: circuit-model well-formedness
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates.CircuitModelTests

set_option autoImplicit false

open Cslib.Complexity.Classes
open Cslib.Complexity.Classes.QuantumGates

#print axioms qGateWellFormed_iff

/-- The CNOT encoding (control qubit 0, target qubit 1) is a well-formed
gate on two qubits. -/
theorem cnotLow_wellFormed_two : QGateWellFormed 2 (0, 1, cnotLowEntries) := by
  exact qGateWellFormed_ctrlLow xGate xGate_unitary (by decide) (by decide)

/-- Nonvacuity: CNOT encoded as a `QGate` on `N = 2` maps `|10⟩` to
`|11⟩` (bitstrings are least-significant-bit first). -/
theorem applyGate_cnotLow_basis_true_false :
    applyGate 2 (0, 1, cnotLowEntries) (basisState [true, false]) =
      basisState [true, true] := by
  funext x
  fin_cases x <;> simp [applyGate, cnotLowEntries, qBit, setBits, basisState,
    qNumOf, matrixOfEntries_entriesOf, complexOfGRatMatrix, ctrlLow, xGate,
    toComplex_gaussRatEnc, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.ext_iff]

#print axioms cnotLow_wellFormed_two
#print axioms applyGate_cnotLow_basis_true_false

end Cslib.Complexity.Classes.QuantumGates.CircuitModelTests
