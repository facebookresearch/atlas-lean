/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DirichletCharacter.DivisorSum

/-!
# Tests for character sums and the divisor sums `1 * χ`

Periodic sums over a full period, the trivial bound at concrete intervals, and the value of the
divisor sum `(1 * χ)(n)` at `n = 0, 1` and at a prime.
-/

@[expose] public section

open Finset

namespace DivisorSumTest

/-- A function on `ZMod 3` summed over three consecutive integers. -/
example (Φ : ZMod 3 → ℤ) : ∑ n ∈ Ico (5 : ℕ) (5 + 3), Φ n = ∑ a, Φ a :=
  ZMod.sum_Ico_add_eq_sum Φ 5

/-- The trivial bound for a nontrivial character. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ‖∑ k ∈ Ico (10 : ℕ) 1000, χ k‖ ≤ q :=
  DirichletCharacter.norm_sum_Ico_le hχ 10 1000

/-- A full period of a nontrivial character sums to `0`. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∑ n ∈ Ico (7 : ℕ) (7 + q), χ n = 0 :=
  DirichletCharacter.sum_Ico_add_modulus_eq_zero hχ 7

example {q : ℕ} (χ : DirichletCharacter ℂ q) : χ.zetaMul 1 = 1 := by
  rw [DirichletCharacter.zetaMul_apply]
  simp

example {q : ℕ} (χ : DirichletCharacter ℂ q) : χ.zetaMul 0 = 0 := by
  rw [DirichletCharacter.zetaMul_apply]
  simp

/-- `(1 * χ)(p) = 1 + χ(p)` at a prime. -/
example {q : ℕ} (χ : DirichletCharacter ℂ q) : χ.zetaMul 5 = 1 + χ 5 := by
  rw [DirichletCharacter.zetaMul_apply, Nat.prime_five.divisors]
  simp

/-- `L(1, χ)` is the limit of the partial sums of `∑ χ(n)/n`. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Filter.Tendsto (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, χ n / (n : ℂ)) Filter.atTop
      (nhds (DirichletCharacter.LFunction χ 1)) :=
  DirichletCharacter.tendsto_sum_Ioc_div_atTop_nhds_LFunction_one hχ

/-- The tail bound at `M = 0`: `‖L(1, χ)‖ ≤ q`. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ q := by
  simpa using DirichletCharacter.norm_LFunction_one_sub_sum_Ioc_le hχ 0

end DivisorSumTest
