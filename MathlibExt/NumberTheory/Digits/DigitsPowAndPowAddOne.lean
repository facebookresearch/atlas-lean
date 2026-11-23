/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs

/-! # Digits of a power of the base and of its successor -/

namespace MetaMathlibExt

/-- **Digits of a power of the base and of its successor.** Let $z \ge 2$ and $n$ be natural
numbers. Then the base-$z$ digits of $z^n$ are a $1$ followed by $n$ zeros, and, if $n \ge 1$,
the base-$z$ digits of $z^n + 1$ are a $1$, then $n - 1$ zeros, then a $1$.

Part (III) of the source theorem is omitted: as printed ($z^n - 1 = (1, 1, \dots, 1)_z$) it is
false for $z \ge 3$, for example $3^2 - 1 = 8 = (2, 2)_3$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 7
(`integers-2024-A69-thm-7`), parts (I) and (II). -/
public theorem digits_pow_and_pow_add_one (z n : ℕ) (hz : 2 ≤ z) :
    Nat.digits z (z ^ n) = List.replicate n 0 ++ [1] ∧
      (1 ≤ n → Nat.digits z (z ^ n + 1) = [1] ++ List.replicate (n - 1) 0 ++ [1]) := by
  have digits_pow (k : ℕ) : Nat.digits z (z ^ k) = List.replicate k 0 ++ [1] := by
    simpa only [mul_one, Nat.digits_of_lt z 1 one_ne_zero hz] using
      Nat.digits_base_pow_mul (k := k) hz Nat.zero_lt_one
  refine ⟨digits_pow n, ?_⟩
  intro hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ', Nat.add_comm _ 1, Nat.digits_add z hz 1 _ hz (Or.inl one_ne_zero), digits_pow]
  simp

end MetaMathlibExt
