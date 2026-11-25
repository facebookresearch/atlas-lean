/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates.ExactGatesTests

set_option autoImplicit false

open scoped Matrix
open Cslib.Complexity.Classes
open Cslib.Complexity.Classes.QuantumGates

/-- A spot entry of low-controlled NOT: control and target both `1` maps to
control `1`, target `1` from input control `1`, target `0`. -/
theorem cnotLow_entry :
    matrixOfEntries cnotLowEntries (1, 1) (1, 0) = 1 := by
  simp only [cnotLowEntries, matrixOfEntries_entriesOf]
  norm_num [complexOfGRatMatrix, ctrlLow, xGate,
    toComplex_gaussRatEnc, Complex.ext_iff]

/-- A spot entry of high-controlled NOT. -/
theorem cnotHigh_entry :
    matrixOfEntries cnotHighEntries (1, 1) (0, 1) = 1 := by
  simp only [cnotHighEntries, matrixOfEntries_entriesOf]
  norm_num [complexOfGRatMatrix, ctrlHigh, xGate,
    toComplex_gaussRatEnc, Complex.ext_iff]

/-- Low-controlled NOT is well-formed on three qubits. -/
theorem cnotLow_wellFormed_three :
    QGateWellFormed 3 (0, 2, cnotLowEntries) := by
  unfold cnotLowEntries
  exact qGateWellFormed_ctrlLow xGate xGate_unitary (by norm_num) (by norm_num)

/-- High-controlled NOT is well-formed on three qubits. -/
theorem cnotHigh_wellFormed_three :
    QGateWellFormed 3 (0, 2, cnotHighEntries) := by
  unfold cnotHighEntries
  exact qGateWellFormed_ctrlHigh xGate xGate_unitary (by norm_num) (by norm_num)

/-- The Toffoli gate list is well-formed for out-of-order indices on five
qubits. -/
theorem toffoli_wellFormed_five_out_of_order :
    ∀ g ∈ toffoliGates 4 0 2, QGateWellFormed 5 g := by
  exact toffoliGates_wellFormed (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- The `(0, 0)` entry in the phase-shifted Hadamard identity. -/
theorem omegaH_zero_zero :
    complexOfGRatMatrix omegaH 0 0 =
      (Complex.exp (Real.pi / 4 * Complex.I) • hadamard) 0 0 := by
  rw [omegaH_eq_smul_hadamard]

#print axioms matrixOfEntries_entriesOf
#print axioms qGateWellFormed_onLow
#print axioms qGateWellFormed_onHigh
#print axioms qGateWellFormed_ctrlLow
#print axioms qGateWellFormed_ctrlHigh
#print axioms controlledGate_wellFormed
#print axioms toffoliGates_wellFormed
#print axioms omegaH_eq_smul_hadamard

end Cslib.Complexity.Classes.QuantumGates.ExactGatesTests
