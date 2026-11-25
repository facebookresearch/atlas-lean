/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.CircuitMatrix

/-!
# Tests: circuit matrices

Concrete checks for the circuit-matrix API: the `qubitSplit` register layout,
the empty-circuit matrix, and the target/control ordering in `QGateWellFormed`.
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates.CircuitMatrixTests

set_option autoImplicit false

open Cslib.Complexity.Classes

/-- Encoded entries of the X gate on the low qubit: the two-qubit matrix swaps
basis indices `0` and `1` and fixes `2` and `3`, in row-major order. -/
def xLowEntries : List (RatEnc × RatEnc) :=
  [((false, 0, 1), (false, 0, 1)), ((false, 1, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 1, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 1, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 1, 1), (false, 0, 1))]

/-- The `qubitSplit` layout sends `(1, 0)` to index `1`. -/
theorem qubitSplit_low_one_val : (qubitSplit 1 1 (1, 0)).val = 1 := by decide

/-- The `qubitSplit` layout sends `(0, 1)` to index `2`. -/
theorem qubitSplit_high_one_val : (qubitSplit 1 1 (0, 1)).val = 2 := by decide

/-- The empty circuit has the identity matrix. -/
theorem circuitMatrix_nil : circuitMatrix 2 [] = 1 := rfl

/-- A gate whose target is above its control is not well-formed: the X gate on
the low qubit with target `1` and control `0` violates the ordering. -/
theorem xLow_target_above_control_not_wellFormed :
    ¬ QGateWellFormed 2 (1, 0, xLowEntries) :=
  fun h => absurd h.1 (by decide)

#print axioms qubitSplit_apply_val
#print axioms applyCircuit_eq_circuitMatrix_mulVec
#print axioms circuitMatrix_mem_unitaryGroup
#print axioms tensorProd_zeroState_zero
#print axioms qubitSplit_low_one_val
#print axioms qubitSplit_high_one_val
#print axioms circuitMatrix_nil
#print axioms xLow_target_above_control_not_wellFormed

end Cslib.Complexity.Classes.QuantumGates.CircuitMatrixTests
