/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.BernsteinVazirani

@[expose] public section

/-!
# Tests for Fourier sampling, Deutsch–Jozsa and Bernstein–Vazirani

The hypotheses are satisfiable in nondegenerate cases: a nonzero hidden string on three bits,
a balanced function on two bits that is not of the form `s·x + b` with `s = 0`, and the
classical counting fact with two queries on three bits.
-/

namespace Cslib.BernsteinVazirani.Tests

open Finset

/-- A nonzero hidden string on three bits. -/
def s₃ : Fin 3 → ZMod 2 := ![1, 0, 1]

example : s₃ ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [s₃] at this

/-- One query recovers `s₃` with certainty. -/
example : fourierSample (fun x => bitDot s₃ x) = Pi.single s₃ 1 := by
  simpa using fourierSample_of_affine s₃ 0 (fun x => bitDot s₃ x) (fun x => by simp)

example : Complex.normSq (fourierSample (fun x => bitDot s₃ x + 1) s₃) = 1 := by
  simpa using normSq_fourierSample_of_affine s₃ 1 (fun x => bitDot s₃ x + 1) (fun _ => rfl) s₃

/-- The first-bit function on two bits is balanced. -/
example : IsBalanced (n := 2) (fun x => x 0) := by
  unfold IsBalanced
  decide

example : fourierSample (n := 2) (fun x => x 0) 0 = 0 :=
  fourierSample_zero_of_isBalanced (by unfold IsBalanced; decide)

/-- The constant function `1`: outcome `0…0` has probability one. -/
example : Complex.normSq (fourierSample (n := 4) (fun _ => 1) 0) = 1 :=
  normSq_fourierSample_zero_of_const 1

/-- The Hadamard transform squares to the identity, here on two qubits. -/
example : hadamard 2 * hadamard 2 = 1 := hadamard_mul_self 2

/-- Two classical evaluations on three bits leave a nonzero string invisible. -/
example : ∃ u : Fin 3 → ZMod 2, u ≠ 0 ∧ ∀ x ∈ ({![1, 0, 0], ![0, 1, 0]} : Finset (Fin 3 → ZMod 2)),
    bitDot u x = 0 :=
  exists_ne_zero_forall_bitDot_eq_zero _ (by decide)

end Cslib.BernsteinVazirani.Tests
