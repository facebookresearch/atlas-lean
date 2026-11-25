/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.LinearCombination

/-!
# An exponent bound for strongly two-near perfect numbers
-/

namespace MetaMathlibExt

/-- **Prime solutions of $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$ satisfy $k < 2a$.** Let $a \le k$
be natural numbers and let $p$ be a prime with $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$, that is,
$p = (2^{k+1} - 2^a - 1)/(1 + 2^{k-a})$. Then $k < 2a$.

The source also assumes that $n = 2^k p$ is strongly $2$-near perfect, that is, that
$\sigma(n) = 2n + d + n/d$ for some divisor $d$ of $n$, where $\sigma$ is the sum of divisors.
This follows from the equation for $p$ by taking $d = 2^a$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 9
(`integers-2024-A61-lem-9`). -/
public theorem lt_two_mul_of_strong_two_near_perfect_form {a k p : ℕ} (hp : p.Prime)
    (hak : a ≤ k) (hform : (p : ℤ) * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1) :
    k < 2 * a := by
  let A : ℤ := 2 ^ a
  let B : ℤ := 2 ^ (k - a)
  let q : ℤ := 2 * A - p
  have hk : a + (k - a) = k := by omega
  have hpow : (2 : ℤ) ^ (k + 1) = 2 * A * B := by
    rw [← hk, pow_succ', pow_add, ← mul_assoc]
  -- The denominator divides the smaller, positive remainder with quotient q.
  have hquot : q * (B + 1) = 3 * A + 1 := by
    rw [hpow] at hform
    change (p : ℤ) * (1 + B) = 2 * A * B - A - 1 at hform
    dsimp only [q]
    linear_combination -hform
  have hA : 0 < A := pow_pos (by decide) _
  have hB : 0 < B := pow_pos (by decide) _
  have hB1 : 0 < B + 1 := by omega
  have hrem : 0 < 3 * A + 1 := by omega
  rw [← hquot] at hrem
  have hq : 0 < q := (mul_pos_iff_of_pos_right hB1).mp hrem
  have ha : 0 < a := by
    by_contra! ha
    have ha0 : a = 0 := by omega
    have hA1 : A = 1 := by simp [A, ha0]
    have hp2 : (2 : ℤ) ≤ p := Int.ofNat_le.mpr hp.two_le
    change 0 < 2 * A - (p : ℤ) at hq
    omega
  have hA2 : 2 ≤ A := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) ha : (2 : ℤ) ^ 1 ≤ 2 ^ a)
  by_contra! hka
  -- In the first two cases the remainder is strictly between adjacent multiples.
  have not_between (m : ℤ) (hl : m * (B + 1) < 3 * A + 1)
      (hu : 3 * A + 1 < (m + 1) * (B + 1)) : False := by
    by_cases hqm : q ≤ m
    · have hle := mul_le_mul_of_nonneg_right hqm hB1.le
      omega
    · have hmq : m + 1 ≤ q := by omega
      have hle := mul_le_mul_of_nonneg_right hmq hB1.le
      omega
  by_cases heq : k - a = a
  · have hBA : B = A := by simp only [A, B, heq]
    apply not_between 2 <;> omega
  by_cases heq' : k - a = a + 1
  · have hBA : B = 2 * A := by simp only [A, B, heq', pow_succ']
    apply not_between 1 <;> omega
  -- Beyond those exponents the remainder is smaller than the first positive multiple.
  have hBA : 4 * A ≤ B := calc
    4 * A = (2 : ℤ) ^ (a + 2) := by
      rw [pow_add, mul_comm]
      rfl
    _ ≤ B := pow_le_pow_right₀ (by decide) (by omega)
  have hle : 1 * (B + 1) ≤ q * (B + 1) :=
    mul_le_mul_of_nonneg_right (by omega) hB1.le
  omega

end MetaMathlibExt
