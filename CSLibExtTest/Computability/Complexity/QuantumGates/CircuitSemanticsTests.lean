/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.CircuitSemantics
public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates

/-!
# Tests: circuit semantics unitarity and Born-probability range
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates.CircuitSemanticsTests

set_option autoImplicit false

open Cslib.Complexity.Classes
open Cslib.Complexity.Classes.QuantumGates

#print axioms applyGate_eq_gateMatrix_mulVec
#print axioms gateMatrix_mem_unitaryGroup
#print axioms sqNorm_applyCircuit
#print axioms sqNorm_bqpInitState
#print axioms acceptProb_le_one

/-- The CNOT circuit on `|10⟩` is a unit vector (norm preservation at a
concrete well-formed gate). -/
theorem sqNorm_cnotLow_basis :
    sqNorm (applyCircuit 2 [(0, 1, cnotLowEntries)]
      (basisState [true, false])) = 1 := by
  rw [sqNorm_applyCircuit]
  · rw [sqNorm_basisState]
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    exact qGateWellFormed_ctrlLow xGate xGate_unitary (by decide) (by decide)

/-- The basis state `|10⟩` (least-significant bit first) accepts with
probability `1`: its output qubit is `1`. -/
theorem acceptProb_basis_true_false :
    acceptProb (basisState [true, false]) = 1 := by
  have hq : qNumOf [true, false] = 1 := rfl
  simp [acceptProb, basisState, hq, Fin.sum_univ_four, qBit]

/-- The basis state `|01⟩` accepts with probability `0`. -/
theorem acceptProb_basis_false_true :
    acceptProb (basisState [false, true]) = 0 := by
  have hq : qNumOf [false, true] = 2 := rfl
  simp [acceptProb, basisState, hq, Fin.sum_univ_four, qBit]

end Cslib.Complexity.Classes.QuantumGates.CircuitSemanticsTests
