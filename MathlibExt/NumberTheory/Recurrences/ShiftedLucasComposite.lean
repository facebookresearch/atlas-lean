/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Basic
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula
import Mathlib.Algebra.Ring.Identities
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Periodic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith

/-! # Composite terms of Lucas sequences and shifted Fibonacci numbers

The terms of the Lucas sequence `U(3, -4)` are composite from index four onward.
We factor five times each term using a difference of squares at even indices and
Sophie Germain's identity at odd indices.

For the shifted Fibonacci sequence, we work modulo the product of 2, 3, 5, 7, 11, 23 and 31.
The Fibonacci pair returns to its initial residues after 240 steps. Over one period the gcd of each
shifted term with this product lies between 2 and 14474, so it is a nontrivial proper divisor.
-/

namespace MetaMathlibExt

namespace lucasU_three_neg_four_composite

/-- If both factors of `5 * u` exceed five, they are both smaller than `u`.
A prime `u` would have to divide one of them. -/
private theorem composite_of_factors {u a b : ℤ} (h : 5 * u = a * b)
    (ha : 5 < a) (hb : 5 < b) : 1 < u ∧ ¬ u.natAbs.Prime := by
  have hau : a < u := by linarith [mul_lt_mul_of_pos_left hb (by omega : 0 < a)]
  have hbu : b < u := by linarith [mul_lt_mul_of_pos_right ha (by omega : 0 < b)]
  refine ⟨by omega, fun hp => ?_⟩
  have hd : u ∣ a * b := h ▸ dvd_mul_left u 5
  obtain hda | hdb := (Int.prime_iff_natAbs_prime.mpr hp).dvd_or_dvd hd
  · exact (Int.le_of_dvd (by omega) hda).not_gt hau
  · exact (Int.le_of_dvd (by omega) hdb).not_gt hbu

end lucasU_three_neg_four_composite

-- Keep the parameter's nonzero proofs inline, as in the original wanted statement.
set_option backward.proofsInPublic true in
/-- **Composite terms of the Lucas sequence $U_n(3, -4)$.** Let $U_n = U_n(3, -4)$ be the
Lucas sequence with $U_0 = 0$, $U_1 = 1$ and $U_{n+2} = 3U_{n+1} + 4U_n$, so that
$U_n = 0, 1, 3, 13, 51, 205, 819, \ldots$. For every natural number $n \ge 4$, $U_n$ is
composite: $U_n > 1$ and $U_n$ is not prime.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 1
(`integers-2025-A42-thm-1`). -/
public theorem lucasU_three_neg_four_composite {n : ℕ} (hn : 4 ≤ n) :
    1 < lucasU ⟨3, -4, by decide⟩ n ∧ ¬ (lucasU ⟨3, -4, by decide⟩ n).natAbs.Prime := by
  have hclosed : 5 * lucasU ⟨3, -4, by decide⟩ n = (4 : ℤ) ^ n - (-1) ^ n := by
    have h := ((lucas_binet_formulas ⟨3, -4, by decide⟩ (4 : ℚ) (-1)
      (by norm_num) (by norm_num)).1 (by norm_num) n).1
    norm_num at h
    rw [mul_comm]
    exact_mod_cast (eq_div_iff (by norm_num : (5 : ℚ) ≠ 0)).mp h
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hk : 2 ≤ k := by omega
    have hpow : (16 : ℤ) ≤ 4 ^ k := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 4) hk
    apply lucasU_three_neg_four_composite.composite_of_factors (a := 4 ^ k - 1) (b := 4 ^ k + 1)
    · rw [hclosed, (even_two_mul k).neg_one_pow, mul_comm 2 k, pow_mul]
      ring
    · omega
    · omega
  · have hk : 2 ≤ k := by omega
    have hpow : (4 : ℤ) ≤ 2 ^ k := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) hk
    have hsq : (16 : ℤ) ≤ (2 ^ k) ^ 2 := pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 4) hpow 2
    have hfour : (4 : ℤ) ^ (2 * k) = ((2 : ℤ) ^ k) ^ 4 := by
      rw [show (4 : ℤ) = 2 ^ 2 by decide, ← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [(odd_two_mul_add_one k).neg_one_pow, pow_succ, hfour] at hclosed
    have hfactor := pow_four_add_four_mul_pow_four (a := (1 : ℤ)) (b := 2 ^ k)
    refine lucasU_three_neg_four_composite.composite_of_factors
      (hclosed.trans (Eq.trans ?_ hfactor)) ?_ ?_
    · ring
    · linarith [sq_nonneg (1 - (2 : ℤ) ^ k)]
    · linarith [sq_nonneg (1 + (2 : ℤ) ^ k)]

namespace ShiftedLucasComposite

private abbrev modulus : ℕ := 2 * 3 * 5 * 7 * 11 * 23 * 31

private theorem fib_periodic : Function.Periodic (fun n => Nat.fib n % modulus) 240 := by
  intro n
  change Nat.ModEq modulus (Nat.fib (n + 240)) (Nat.fib n)
  induction n using Nat.twoStepInduction with
  | zero => decide +kernel
  | one => decide +kernel
  | more n ih₀ ih₁ =>
    rw [Nat.add_right_comm n 2 240, Nat.fib_add_two, Nat.fib_add_two (n := n)]
    exact ih₀.add ih₁

private theorem gcd_bounds : ∀ r < 240,
    2 ≤ Nat.gcd (Nat.fib r + 14475) modulus ∧ Nat.gcd (Nat.fib r + 14475) modulus < 14475 := by
  decide +kernel

end ShiftedLucasComposite

open ShiftedLucasComposite

/-- **Fibonacci numbers shifted by $14475$ are never prime.** Let $F_n$ be the $n$-th
Fibonacci number, with $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$. For every
natural number $n$, the number $F_n + 14475$ is not prime.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 5
(`integers-2025-A42-thm-5`). -/
public theorem fib_add_14475_not_prime (n : ℕ) : ¬ (Nat.fib n + 14475).Prime := by
  have h : Nat.ModEq modulus (Nat.fib (n % 240)) (Nat.fib n) := fib_periodic.map_mod_nat n
  have bounds := gcd_bounds (n % 240) (Nat.mod_lt _ (by decide))
  rw [(h.add_right 14475).gcd_eq] at bounds
  exact Nat.not_prime_of_dvd_of_lt (Nat.gcd_dvd_left _ _) bounds.1 (by omega)

end MetaMathlibExt
