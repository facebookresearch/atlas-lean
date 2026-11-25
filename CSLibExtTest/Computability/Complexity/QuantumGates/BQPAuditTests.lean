/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.BQPAudit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Tests: BQP class audit
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates.BQPAuditTests

set_option autoImplicit false

open Cslib.Complexity.Classes
open Cslib.Complexity.Classes.QuantumGates

#print axioms mem_BQP_iff
#print axioms bqp_witness_acceptProb_mem_Icc
#print axioms acceptProb_applyGate_xLow

/-- With no gates, the acceptance probability on input `[true]` with one
ancilla is `1`: the output qubit starts at `1`. -/
theorem acceptProb_bqpInitState_true :
    acceptProb (applyCircuit (1 + 1) ([] : List QGate)
      (bqpInitState [true] 1)) = 1 := by
  have hnil : applyCircuit (1 + 1) ([] : List QGate) (bqpInitState [true] 1)
      = bqpInitState [true] 1 := rfl
  rw [hnil]
  simp only [acceptProb]
  show (Finset.sum Finset.univ (fun s : Fin 4 => if qBit 0 s.val = 1 then
      (starRingEnd Complex (bqpInitState [true] 1 s) *
        bqpInitState [true] 1 s).re else 0)) = 1
  rw [Fin.sum_univ_four]
  simp [bqpInitState, tensorProd, basisState, zeroState, qNumOf, qBit]

/-- Flipping the output qubit of `|10⟩` makes the acceptance probability
`0`. -/
theorem acceptProb_xLow_basis_true_false :
    acceptProb (applyGate 2 (0, 1, xLowEntries)
      (basisState [true, false])) = 0 := by
  simp only [acceptProb]
  show (Finset.sum Finset.univ (fun s : Fin 4 => if qBit 0 s.val = 1 then
      (starRingEnd Complex ((applyGate 2 (0, 1, xLowEntries)
        (basisState [true, false])) s) *
        ((applyGate 2 (0, 1, xLowEntries) (basisState [true, false])) s)).re
      else 0)) = 0
  rw [Fin.sum_univ_four]
  simp [applyGate, xLowEntries, matrixOfEntries_entriesOf, complexOfGRatMatrix,
    onLow, xGate, toComplex_gaussRatEnc, basisState, qNumOf, setBits, qBit,
    Fintype.sum_prod_type, Fin.sum_univ_two]

end Cslib.Complexity.Classes.QuantumGates.BQPAuditTests
