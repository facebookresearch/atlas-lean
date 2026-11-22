/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.BitFlipCode

@[expose] public section

/-!
# Tests for the three-qubit bit-flip code

* The code projector is nonzero: it fixes `|000⟩` and `|111⟩`, so the correctability theorem is
  about a two-dimensional code, not the zero code.
* A bit flip on one qubit together with a bit flip on the other two is not correctable: their
  product `X₁X₂X₃` maps `|000⟩` to `|111⟩`, so the Knill–Laflamme condition fails. The weight
  restriction in `isCorrectable_bitFlip` is therefore needed.
* A coherent error `c I + d X₁` (for instance a small rotation of the first qubit) is correctable,
  since correctable families are linearly closed.
* `(X^a)ᴴ X^a = 1`: each bit flip is unitary (a special case of the Pauli product formula).
-/

namespace Cslib.CodingTheory.BitFlip.Tests

open scoped Matrix
open Matrix Cslib.CodingTheory.CSS MathlibExt.QuantumInformation.Finite.KnillLaflamme

example : codeProjector 0 0 = 1 ∧ codeProjector 1 1 = 1 := by
  simp [codeProjector]

example : codeProjector ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [codeProjector] at this

example (a : Fin 3 → ZMod 2) : (pauli a 0)ᴴ * pauli a 0 = 1 := by
  rw [QuantumCode.conjTranspose_pauli_mul_pauli, add_self_eq_zero, add_zero, zero_dotProduct,
    sign_zero, one_smul]
  ext u v
  simp [pauli, Matrix.one_apply, sign_zero]

/-- Flip pattern of qubit 0. -/
def flip0 : Fin 3 → ZMod 2 := ![1, 0, 0]

/-- Flip pattern of qubits 1 and 2. -/
def flip12 : Fin 3 → ZMod 2 := ![0, 1, 1]

example : ¬ IsCorrectable codeProjector ![pauli flip0 0, pauli flip12 0] := by
  intro h
  obtain ⟨c, hc⟩ :=
    knillLaflamme_of_isCorrectable codeProjector_isProj.1 codeProjector_isProj.2 h 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  rw [Matrix.mul_assoc codeProjector, QuantumCode.conjTranspose_pauli_mul_pauli, zero_dotProduct,
    sign_zero, one_smul, add_zero] at hc
  have h00 := congrFun (congrFun hc 0) 0
  have h10 := congrFun (congrFun hc 1) 0
  have hsum : flip0 + flip12 = 1 := by decide
  simp only [hsum, codeProjector, diagonal_mul, mul_diagonal, pauli, of_apply, zero_dotProduct,
    sign_zero, Matrix.smul_apply, diagonal_apply, smul_eq_mul] at h00 h10
  norm_num at h00 h10

example (c d : ℂ) :
    IsCorrectable codeProjector fun _ : Unit => c • pauli 0 0 + d • pauli (Pi.single 0 1) 0 :=
  isCorrectable_bitFlip.of_forall_mem_span fun _ =>
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨some 0, rfl⟩))

end Cslib.CodingTheory.BitFlip.Tests
