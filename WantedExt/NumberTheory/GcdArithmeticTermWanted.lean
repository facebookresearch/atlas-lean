/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Inverse

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **The gcd-term sequence.** For natural numbers $a$, $b$ and $n$, $s_{a,b}(n)$ is the rational
number that is the coefficient of $z^n$ in the inverse of the formal power series
$(z^a - 1)(z^b - 1)$ over $\mathbb{Q}$. For $a, b \ge 1$ this series has constant coefficient $1$,
so $s_{a,b}$ is the coefficient sequence of $f_{a,b}(z) = 1 / ((z^a - 1)(z^b - 1))$. If $a = 0$
or $b = 0$ the series is $0$, whose inverse is taken to be $0$, so $s_{a,b}(n) = 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Section 2 (definition of `s_{a,b}`). -/
public noncomputable def gcdTermSeq (a b n : ℕ) : ℚ :=
  coeff n (((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1))⁻¹

/-- **Initial value of the gcd-term sequence.** For natural numbers $a, b \ge 1$, the gcd-term
sequence satisfies $s_{a,b}(0) = 1$.

Source: Prunescu and Shunia, *Arithmetic-Term Representations for the Greatest Common Divisor*,
INTEGERS 26 (2026), Article A96, Section 2. -/
public theorem gcdTermSeq_zero (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : gcdTermSeq a b 0 = 1 := by
  have ha' : a ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  simp [gcdTermSeq, ha', hb']

/-- **Generating function of the gcd-term sequence.** For natural numbers $a, b \ge 1$, in the
ring $\mathbb{Q}[[z]]$ of formal power series, the gcd-term sequence $s_{a,b}$ satisfies
$$
(z^a - 1)(z^b - 1) \sum_{n \ge 0} s_{a,b}(n) z^n = 1.
$$

Source: Prunescu and Shunia, *Arithmetic-Term Representations for the Greatest Common Divisor*,
INTEGERS 26 (2026), Article A96, Section 2. -/
public theorem mul_mk_gcdTermSeq (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1) * PowerSeries.mk (gcdTermSeq a b) = 1 := by
  have ha' : a ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  have hmk : PowerSeries.mk (gcdTermSeq a b) =
      (((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1))⁻¹ := by
    ext n
    simp [gcdTermSeq]
  rw [hmk]
  apply PowerSeries.mul_inv_cancel
  simp [ha', hb']

/-- **The gcd-term sequence is integral and recovers the gcd.** Let $a, b \ge 1$ be natural
numbers and let $s_{a,b}$ be the gcd-term sequence. Every value $s_{a,b}(n)$ is a natural number,
and $s_{a,b}(ab) = \gcd(a, b) + 1$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Lemma 4. -/
public theorem_wanted gcdTermSeq_natural_and_eq_gcd_add_one (a b : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    (∀ n, ∃ m : ℕ, gcdTermSeq a b n = m) ∧ gcdTermSeq a b (a * b) = Nat.gcd a b + 1

/-- **The gcd-term sequence is bounded by $n + 1$.** Let $a, b \ge 1$ be natural numbers, at least
one of them greater than $1$, and let $s_{a,b}$ be the gcd-term sequence. For every natural
number $n$, $s_{a,b}(n) \le s_{1,1}(n) = n + 1$, and $s_{a,b}(n) = s_{1,1}(n)$ only if $n = 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Lemma 5. -/
public theorem_wanted gcdTermSeq_le_gcdTermSeq_one_one (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 1 < a ∨ 1 < b) (n : ℕ) :
    gcdTermSeq a b n ≤ gcdTermSeq 1 1 n ∧ gcdTermSeq 1 1 n = n + 1 ∧
      (gcdTermSeq a b n = gcdTermSeq 1 1 n → n = 0)

/-- **Arithmetic term for the gcd in base $5$.** For all natural numbers $a, b \ge 1$,
$$
\gcd(a, b) + 1 = \left\lfloor \frac{5^{ab(ab+a+b)}}{(5^{a^2 b} - 1)(5^{a b^2} - 1)} \right\rfloor
\bmod 5^{ab},
$$
that is, $\gcd(a, b)$ is one less than the remainder of this floor modulo $5^{ab}$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Theorem 1. -/
public theorem_wanted gcd_add_one_eq_floor_div_mod_five (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.gcd a b + 1 =
      5 ^ (a * b * (a * b + a + b)) / ((5 ^ (a ^ 2 * b) - 1) * (5 ^ (a * b ^ 2) - 1)) %
        5 ^ (a * b)

/-- **Second arithmetic term for the gcd in base $5$.** For all natural numbers $a, b \ge 1$,
$$
\gcd(a, b) = \Big( \big( (-5^{ab(ab+a+b)}) \bmod \big( (5^{a^2 b} - 1)(5^{a b^2} - 1) \big) \big)
\bmod 5^{ab} \Big) - 2
$$
in the integers, where $x \bmod m$ is the remainder of $x$ in $\{0, \dots, m - 1\}$ for $m > 0$,
also when $x < 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Corollary 1. -/
public theorem_wanted gcd_eq_neg_emod_emod_five_sub_two (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (Nat.gcd a b : ℤ) =
      (-(5 : ℤ) ^ (a * b * (a * b + a + b))) %
            (((5 : ℤ) ^ (a ^ 2 * b) - 1) * ((5 : ℤ) ^ (a * b ^ 2) - 1)) % (5 : ℤ) ^ (a * b) - 2

/-- **The gcd terms in bases $2$, $3$ and $4$.** Let $c \in \{2, 3, 4\}$, let $a, b \ge 1$ be
natural numbers, and put $E = ab(ab + a + b)$ and $D = (c^{a^2 b} - 1)(c^{a b^2} - 1)$. Then the
identity
$$
\gcd(a, b) = \left( \lfloor c^E / D \rfloor \bmod c^{ab} \right) - 1
$$
holds if and only if $(a, b) \ne (1, 1)$, and the identity
$$
\gcd(a, b) = \big( ((-c^E) \bmod D) \bmod c^{ab} \big) - 2
$$
holds if and only if $(a, b) \ne (1, 1)$. Both identities are read in the integers, where
$x \bmod m$ is the remainder of $x$ in $\{0, \dots, m - 1\}$ for $m > 0$, also when $x < 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Corollary 2. -/
public theorem_wanted gcd_arithmetic_terms_small_bases (c : ℤ) (hc : c = 2 ∨ c = 3 ∨ c = 4)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((Nat.gcd a b : ℤ) =
        c ^ (a * b * (a * b + a + b)) / ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 1 ↔ (a, b) ≠ (1, 1)) ∧
      ((Nat.gcd a b : ℤ) =
        (-c ^ (a * b * (a * b + a + b))) % ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 2 ↔ (a, b) ≠ (1, 1))

end

end MetaMathlibExt
