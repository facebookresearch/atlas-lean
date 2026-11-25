/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.ZMod.Basic

/-! # Divisibility of later generalized Fermat numbers -/

namespace MetaMathlibExt

-- Retain the source's bounds and the original statement's named arguments.
set_option linter.unusedVariables false in
/-- **Divisibility of later generalized Fermat numbers.** For natural numbers $a$, $b$ and $m$
write $F_m(a, b) = a^{b^m} + 1$. Let $a, b, D \ge 2$ and $n$ be natural numbers such that $D$
divides $F_n(a, b)$. If $b$ is odd, then $D$ divides $F_{n+k}(a, b)$ for every $k \ge 1$. If $b$
is even and $D \ge 3$, then $D$ does not divide $F_{n+k}(a, b)$ for any $k \ge 1$.

The source states the even case for $D \ge 2$; its proof gives $F_{n+k}(a, b) \equiv 2 \pmod D$,
which excludes only $D = 2$, and the even case is false there: for $a = 3$, $b = 2$, $n = 0$ and
$k = 1$, $2$ divides both $F_0(3, 2) = 4$ and $F_1(3, 2) = 10$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 7 (`integers-2026-A77-thm-7`). -/
public theorem dvd_pow_pow_add_one_shift {a b D n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hD : 2 ≤ D) (h : D ∣ a ^ b ^ n + 1) :
    (Odd b → ∀ k, 1 ≤ k → D ∣ a ^ b ^ (n + k) + 1) ∧
      (Even b → 3 ≤ D → ∀ k, 1 ≤ k → ¬ D ∣ a ^ b ^ (n + k) + 1) := by
  have hz : (a : ZMod D) ^ b ^ n = -1 := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff (a ^ b ^ n + 1) D).mpr h
  -- Klaška's Equation (16): all later residues are determined by the parity of b ^ k.
  have hshift (k : ℕ) : ((a ^ b ^ (n + k) + 1 : ℕ) : ZMod D) = (-1) ^ b ^ k + 1 := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, pow_add, pow_mul, hz]
  refine ⟨?_, ?_⟩
  · intro hOdd k _
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [hshift, (hOdd.pow (n := k)).neg_one_pow, neg_add_cancel]
  · intro hEven hD' k hk hdvd
    have hpow : Even (b ^ k) := hEven.pow_of_ne_zero (Nat.ne_of_gt hk)
    have htwo : (2 : ZMod D) = 0 := by
      simpa only [hshift, hpow.neg_one_pow, one_add_one_eq_two] using
        (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hD'
      ((ZMod.natCast_eq_zero_iff 2 D).mp (by simpa only [Nat.cast_two] using htwo))

end MetaMathlibExt
