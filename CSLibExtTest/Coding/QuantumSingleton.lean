/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Coding.QuantumSingleton
import CSLibExtTest.Coding.QuantumCodeDistanceTests

/-!
# Tests for the quantum Singleton bound

The entire two-qubit space attains the bound at distance one. Even encoding just one logical
qubit in two physical qubits precludes detection of every single-qubit Pauli error.
-/

open scoped Matrix
open Matrix Cslib.CodingTheory.QuantumCode Cslib.CodingTheory.QuantumSingletonWanted

namespace Cslib.CodingTheory.QuantumSingletonWanted.Tests

private abbrev TwoQubitOp := Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ

example (d : ℕ) : HasDistanceAtLeast (1 : TwoQubitOp) d ↔ d ≤ 1 := by
  constructor
  · intro hd
    have hdim : Module.finrank ℂ (LinearMap.range (Matrix.toLin' (1 : TwoQubitOp))) = 2 ^ 2 := by
      rw [Matrix.toLin'_one, LinearMap.range_id, finrank_top, Module.finrank_fintype_fun_eq_card]
      simp
    have := quantum_singleton_bound 1 conjTranspose_one (Matrix.mul_one 1) (by decide) hdim hd
    omega
  · intro hd a b hw
    exact Cslib.CodingTheory.QuantumCode.Tests.hasDistanceAtLeast_one 1 (Matrix.mul_one 1)
      a b (hw.trans_le hd)

example (P : TwoQubitOp) (hP : Pᴴ = P) (hPP : P * P = P)
    (hdim : Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) = 2 ^ 1) :
    ¬ HasDistanceAtLeast P 2 := by
  intro hd
  have := quantum_singleton_bound P hP hPP (by decide) hdim hd
  omega

end Cslib.CodingTheory.QuantumSingletonWanted.Tests
