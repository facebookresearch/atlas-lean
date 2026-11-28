/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.EncodingPlumbing

/-!
# Tests: QGate/RatEnc encoding plumbing
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates.EncodingPlumbingTests

set_option autoImplicit false

open Cslib.Complexity.Classes
open Cslib.Complexity.Classes.QuantumGates

#print axioms qGateWellFormed_entriesOf
#print axioms exists_gratMatrix_eq
#print axioms exists_wellFormed_gate_matrixOfEntries_eq

/-- The identity matrix encodes as a well-formed gate on qubits `0, 1` of a
three-qubit register, decoding back to the identity. -/
theorem exists_wellFormed_identity_gate :
    ∃ e : List (RatEnc × RatEnc),
      QGateWellFormed 3 (0, 1, e) ∧
        matrixOfEntries e = (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ∧
        e.length = 16 := by
  have hM : ∀ p q : Fin 2 × Fin 2,
      ∃ a b : ℚ, (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) p q =
        ⟨(a : ℝ), (b : ℝ)⟩ := by
    intro p q
    by_cases h : p = q
    · subst h
      exact ⟨1, 0, by rw [Matrix.one_apply_eq, Complex.ext_iff]; simp⟩
    · exact ⟨0, 0, by rw [Matrix.one_apply_ne h, Complex.ext_iff]; simp⟩
  have hU : star (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) *
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 1 := by
    rw [star_one, one_mul]
  exact exists_wellFormed_gate_matrixOfEntries_eq
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) hU hM (by norm_num) (by norm_num)

end Cslib.Complexity.Classes.QuantumGates.EncodingPlumbingTests
