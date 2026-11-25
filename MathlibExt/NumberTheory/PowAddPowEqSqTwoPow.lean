/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import MathlibExt.NumberTheory.PowAddPowEqSq
import MathlibExt.NumberTheory.PowAddPowEqSqEvenExponent
import MathlibExt.NumberTheory.ThreePowAddThirtyfivePow
import MathlibExt.NumberTheory.TwoPowAddFifteenPow

/-!
# Solutions of `2^x + (5p)^y = z^2` for primes `p ≡ 3 (mod 4)`

`two_pow_solutions` classifies the natural-number solutions of `2^x + (5p)^y = z^2` when `p` is
a prime congruent to `3` modulo `4`. This is Theorem 3 of Suton Tadee, "On the Diophantine
Equation `n^x + (5p)^y = z^2`", *INTEGERS* 24 (2024), Article A68
(<https://math.colgate.edu/~integers/vol24.html>).

For `p = 3` the statement is the classification of `2^x + 15^y = z^2`
(`two_pow_add_fifteen_pow`). For `p ≠ 3`, the cases `y = 0` and `x = 0` are the equations
`2^x + 1 = z^2` (`MetaMathlibExt.two_pow_add_one_eq_sq`) and `1 + (5p)^y = z^2`
(`one_add_pow_eq_sq`). When both exponents are positive, `x` is even (`even_of_pos_exp`), so
`2^x ≡ 0 (mod 4)`. Since `5p ≡ -1 (mod 4)` and every square is `0` or `1` modulo `4`, `y` is
even as well. Then `2^x ≡ (5p)^y ≡ 1 (mod 3)`, so the sum is `2` modulo `3`, which no square is.
-/

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

/-- **Solutions of $2^x + (5p)^y = z^2$ for $p \equiv 3 \pmod 4$.** Let $p$ be a prime with
$p \equiv 3 \pmod 4$. For natural numbers $x$, $y$, $z$, $2^x + (5p)^y = z^2$ holds if and
only if $(x, y, z) = (3, 0, 3)$, or $p = 3$ and $(x, y, z) = (6, 2, 17)$, or $x = 0$, $y = 1$
and $z^2 = 5p + 1$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Theorem 3. -/
public theorem two_pow_solutions (p x y z : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) :
    2 ^ x + (5 * p) ^ y = z ^ 2 ↔
      (x = 3 ∧ y = 0 ∧ z = 3) ∨
        (p = 3 ∧ x = 6 ∧ y = 2 ∧ z = 17) ∨
        (x = 0 ∧ y = 1 ∧ z ^ 2 = 5 * p + 1) := by
  rcases eq_or_ne p 3 with rfl | hp3
  · -- For `p = 3` this is the classification of `2^x + 15^y = z^2`.
    have hz : z ^ 2 = 16 ↔ z = 4 := by
      rw [show (16 : ℕ) = 4 ^ 2 by norm_num, Nat.pow_left_inj two_ne_zero]
    simp only [Nat.reduceMul, Nat.reduceAdd, two_pow_add_fifteen_pow, hz, true_and]
    tauto
  constructor
  · intro h
    by_cases hy : y = 0
    · subst y
      obtain ⟨rfl, rfl⟩ := (MetaMathlibExt.two_pow_add_one_eq_sq x z).mp h
      exact Or.inl ⟨rfl, rfl, rfl⟩
    by_cases hx : x = 0
    · subst x
      exact Or.inr (Or.inr ⟨rfl, (one_add_pow_eq_sq p y z hp (by omega)).mp h⟩)
    exfalso
    obtain ⟨k, rfl⟩ := even_iff_two_dvd.mp
      (even_of_pos_exp 2 p x y z hp (Or.inl rfl) (Nat.pos_of_ne_zero hy) h)
    rcases Nat.even_or_odd' y with ⟨m, rfl | rfl⟩
    · -- Both exponents are even, so both powers are `1` modulo `3`.
      have h5p : 5 * p % 3 = 1 ∨ 5 * p % 3 = 2 := by
        have h3 : ¬3 ∣ p := fun h3 =>
          hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
        omega
      have h2 : 2 ^ (2 * k) % 3 = 1 := by
        rw [pow_mul, Nat.pow_mod]
        norm_num
      have h5 : (5 * p) ^ (2 * m) % 3 = 1 := by
        have hsq : (5 * p) ^ 2 % 3 = 1 := by
          rw [Nat.pow_mod]
          rcases h5p with h | h <;> rw [h]
        rw [pow_mul, Nat.pow_mod, hsq]
        simp
      have hz : z ^ 2 % 3 = 0 ∨ z ^ 2 % 3 = 1 := by
        have hz3 : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
        rcases hz3 with h | h | h <;> rw [Nat.pow_mod, h] <;> decide
      omega
    · -- The first power is `0` and the second is `3` modulo `4`.
      have h2 : 4 ∣ 2 ^ (2 * k) := by
        rw [pow_mul]
        exact dvd_pow_self _ (by omega)
      have h5 : (5 * p) ^ (2 * m + 1) % 4 = 3 := by
        rw [Nat.pow_mod, show 5 * p % 4 = 3 by omega, pow_succ, pow_mul, Nat.mul_mod,
          Nat.pow_mod]
        norm_num
      have hz : z ^ 2 % 4 = 0 ∨ z ^ 2 % 4 = 1 := by
        have hz4 : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
        rcases hz4 with h | h | h | h <;> rw [Nat.pow_mod, h] <;> decide
      omega
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨h3, -⟩ | ⟨rfl, rfl, hz⟩)
    · norm_num
    · exact absurd h3 hp3
    · rw [pow_zero, pow_one, hz, add_comm]

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
