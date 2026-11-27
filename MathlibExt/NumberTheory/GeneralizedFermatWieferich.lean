/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.ZMod.LocalRing
import MathlibExt.NumberTheory.WieferichOrder

/-! # Squared prime factors of generalized Fermat numbers with exponent base two -/

namespace MetaMathlibExt

/-- **Squared prime factors of $a^{2^n} + 1$.** Let $p$ be an odd prime, let $a$ be a natural
number not divisible by $p$, and let $n$ be a natural number. Then $p^2$ divides $a^{2^n} + 1$ if
and only if $a^{p-1} \equiv 1 \pmod{p^2}$ (that is, $p$ is a Wieferich prime to base $a$) and the
multiplicative order of $a$ modulo $p$ is $2^{n+1}$.

The congruence $a^{p-1} \equiv 1 \pmod{p^2}$ is the source's equation (8) defining $p \in W(a)$.
The source assumes $a \ge 2$; for $a = 1$ both sides are false.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 5 (`integers-2026-A77-thm-5`). -/
public theorem sq_dvd_pow_two_pow_add_one_iff_wieferich {a n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpa : ¬ p ∣ a) :
    p ^ 2 ∣ a ^ 2 ^ n + 1 ↔ a ^ (p - 1) ≡ 1 [MOD p ^ 2] ∧ orderOf (a : ZMod p) = 2 ^ (n + 1) := by
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le hp2.symm
  have : Fact (2 < p) := ⟨hp_gt⟩
  have : Fact (2 < p ^ 2) := ⟨hp_gt.trans_le (Nat.le_self_pow two_ne_zero p)⟩
  have : Fact p.Prime := ⟨hp⟩
  -- Modulo any divisor greater than two, the half power is -1 and its square is 1.
  have order_of_dvd (m : ℕ) [Fact (2 < m)] (hm : m ∣ a ^ 2 ^ n + 1) :
      orderOf (a : ZMod m) = 2 ^ (n + 1) := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hm
    have hneg := eq_neg_of_add_eq_zero_left hm
    apply orderOf_eq_prime_pow
    · rw [hneg]
      exact ZMod.neg_one_ne_one
    · rw [pow_succ, pow_mul, hneg]
      simp
  rw [pow_sub_one_modEq_one_sq_iff_orderOf_eq hp hpa]
  constructor
  · intro h
    have horder := order_of_dvd p ((dvd_pow_self p two_ne_zero).trans h)
    exact ⟨(order_of_dvd (p ^ 2) h).trans horder.symm, horder⟩
  · rintro ⟨heq, horder⟩
    let x := (a : ZMod (p ^ 2)) ^ 2 ^ n
    have hsq : x ^ 2 = 1 := by
      simpa only [heq, horder, pow_succ 2 n, pow_mul, x] using
        pow_orderOf_eq_one (a : ZMod (p ^ 2))
    -- The reduction of x - 1 is nonzero modulo p, so x - 1 is a unit modulo p².
    have hunit : IsUnit (x - 1) := by
      apply (ZMod.isLocalHom_castHom_pow (n := p) two_ne_zero).map_nonunit
      simp only [x, map_sub, map_pow, map_natCast, map_one, isUnit_iff_ne_zero, sub_ne_zero]
      apply pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
      rw [horder]
      exact Nat.pow_lt_pow_succ (by decide)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    change x + 1 = 0
    apply hunit.mul_left_eq_zero.mp
    rw [← sq_sub_sq, hsq, one_pow, sub_self]

end MetaMathlibExt
