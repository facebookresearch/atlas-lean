/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import MathlibExt.NumberTheory.JacobsthalLucasNumber
import Mathlib.Tactic.Ring

/-! # Oresme–Jacobsthal–Lucas congruence -/

namespace MetaMathlibExt

/-- **Powers of two times Jacobsthal–Lucas numbers modulo 9.** Let $j_m$ denote the
Jacobsthal–Lucas numbers. For every natural number $n$, $2^n j_{n+1} \equiv 1 \pmod{9}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 6.5 (`fq-2024-cookbacon061124-cor-6.5`). -/
public theorem two_pow_mul_jacobsthalLucasNumber_succ_modEq_nine (n : ℕ) :
    2 ^ n * jacobsthalLucasNumber (n + 1) ≡ 1 [MOD 9] := by
  let T (k : ℕ) : ℕ := 2 ^ k * jacobsthalLucasNumber (k + 1)
  have hT (k : ℕ) : T (k + 2) = 2 * T (k + 1) + 8 * T k := by
    dsimp only [T]
    rw [jacobsthalLucasNumber.eq_3 (k + 1), pow_succ 2 (k + 1), pow_succ 2 k]
    ring
  have h10 : 2 * 1 + 8 * 1 ≡ 1 [MOD 9] := by decide
  have h (k : ℕ) : (T k ≡ 1 [MOD 9]) ∧ (T (k + 1) ≡ 1 [MOD 9]) := by
    induction k with
    | zero => exact ⟨by decide, by decide⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [hT k]
      exact ((ih.2.mul_left 2).add (ih.1.mul_left 8)).trans h10
  exact (h n).1

end MetaMathlibExt
