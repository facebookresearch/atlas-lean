/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Fermat
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.NumberTheory.WieferichPrime

/-!
# Notes on Jakóbczyk's hypothesis on Fermat numbers

Statements from Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat
Numbers*, INTEGERS 26 (2026), Article A77, about the Fermat numbers
`F_n = 2^{2^n} + 1` (Mathlib's `Nat.fermatNumber`), their generalizations
`F_n(a, b) = a^{b^n} + 1`, and Wieferich primes to base `2` (`Nat.IsWieferichPrime`, i.e.
`p² ∣ 2^{p-1} - 1`) and to base `a` (`a^{p-1} ≡ 1 (mod p²)`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Warren–Bray congruence for prime divisors of Fermat numbers.** Let $F_n = 2^{2^n} + 1$ be
the $n$-th Fermat number. For every $n \ge 2$ and every odd prime $p$ dividing $F_n$, we have
$2^{(p-1)/2} \equiv 1 \pmod{F_n}$. This result is due to Warren and Bray (1967).

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 2 (`integers-2026-A77-thm-2`), citing
Warren and Bray. -/
public theorem_wanted two_pow_half_modEq_one_fermatNumber {n p : ℕ} (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.fermatNumber n) :
    2 ^ ((p - 1) / 2) ≡ 1 [MOD Nat.fermatNumber n]

/-- **Squared prime factors of Fermat numbers.** Let $F_n = 2^{2^n} + 1$ be the $n$-th Fermat
number, and let $p$ be a prime dividing $F_n$. Then $p^2$ divides $F_n$ if and only if
$2^{p-1} \equiv 1 \pmod{p^2}$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 3 (`integers-2026-A77-thm-3`), citing
Křížek, Luca, and Somer. -/
public theorem_wanted sq_dvd_fermatNumber_iff {n p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.fermatNumber n) :
    p ^ 2 ∣ Nat.fermatNumber n ↔ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2]

/-- **Squared prime factors of Fermat numbers via Wieferich primes and orders.** Let
$F_n = 2^{2^n} + 1$ be the $n$-th Fermat number. For every natural number $n$ and every odd prime
$p$, $p^2$ divides $F_n$ if and only if $p$ is a Wieferich prime (to base $2$) and the
multiplicative order of $2$ modulo $p$ is $2^{n+1}$.

This follows from the criterion that a prime $p$ dividing $F_n$ satisfies $p^2 \mid F_n$ exactly
when $2^{p-1} \equiv 1 \pmod{p^2}$, since an odd prime $p$ divides $F_n$ exactly when the order
of $2$ modulo $p$ is $2^{n+1}$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 5, Equation (11)
(`integers-2026-A77-thm-5`). -/
public theorem_wanted sq_dvd_fermatNumber_iff_wieferich_orderOf {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    p ^ 2 ∣ Nat.fermatNumber n ↔ p.IsWieferichPrime ∧ orderOf (2 : ZMod p) = 2 ^ (n + 1) := by
  have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  have : Fact p.Prime := ⟨hp⟩
  have hF : ((Nat.fermatNumber n : ℕ) : ZMod p) = (2 : ZMod p) ^ 2 ^ n + 1 := by
    simp [Nat.fermatNumber]
  have hdvd : p ∣ Nat.fermatNumber n ↔ orderOf (2 : ZMod p) = 2 ^ (n + 1) := by
    rw [← ZMod.natCast_eq_zero_iff, hF]
    constructor
    · intro h
      have h1 : (2 : ZMod p) ^ 2 ^ n = -1 := eq_neg_of_add_eq_zero_left h
      refine orderOf_eq_prime_pow ?_ ?_
      · rw [h1]; exact ZMod.neg_one_ne_one
      · rw [pow_succ, pow_mul, h1]; norm_num
    · intro h
      have h2 : (2 : ZMod p) ^ 2 ^ (n + 1) = 1 := by rw [← h]; exact pow_orderOf_eq_one _
      have h3 : (2 : ZMod p) ^ 2 ^ n ≠ 1 := by
        intro h4
        have h7 := Nat.le_of_dvd (by positivity) (h ▸ orderOf_dvd_of_pow_eq_one h4)
        have h8 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have h5 : (2 : ZMod p) ^ 2 ^ n * (2 : ZMod p) ^ 2 ^ n = 1 := by
        rw [← pow_add, ← two_mul, ← pow_succ']; exact h2
      rcases mul_self_eq_one_iff.mp h5 with h6 | h6
      · exact absurd h6 h3
      · rw [h6]; ring
  rw [Nat.isWieferichPrime_iff_modEq]
  constructor
  · intro h
    have hpd : p ∣ Nat.fermatNumber n := (dvd_pow_self p two_ne_zero).trans h
    exact ⟨⟨hp, (❰sq_dvd_fermatNumber_iff❱ hp hpd).mp h⟩, hdvd.mp hpd⟩
  · rintro ⟨⟨-, hw⟩, ho⟩
    exact (❰sq_dvd_fermatNumber_iff❱ hp (hdvd.mpr ho)).mpr hw

/-- **Greatest common divisors of generalized Fermat numbers.** For natural numbers $a$, $b$ and
$k$ write $F_k(a, b) = a^{b^k} + 1$, and let $a, b \ge 2$ and $m$, $n$ be natural numbers. If
$n < m$ and $a$ and $b$ are both even, then $\gcd(F_m(a, b), F_n(a, b)) = 1$. If $n < m$, $a$ is
odd and $b$ is even, then $\gcd(F_m(a, b), F_n(a, b)) = 2$. If $n \le m$ and $b$ is odd, then
$\gcd(F_m(a, b), F_n(a, b)) = F_n(a, b)$.

The source assumes $a, b > 2$ and $0 \le n \le m$; its proof uses only $a, b \ge 2$ and treats
$m > n$ ("Since $m > n$"), and the first two cases fail for $m = n$: for $a = b = 4$ and
$m = n = 0$ the gcd is $\gcd(5, 5) = 5$, and for $a = 3$, $b = 4$ and $m = n = 0$ it is
$\gcd(4, 4) = 4$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Proposition 1 (`integers-2026-A77-prop-1`). -/
public theorem_wanted gcd_pow_pow_add_one {a b m n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (n < m → Even a → Even b → Nat.gcd (a ^ b ^ m + 1) (a ^ b ^ n + 1) = 1) ∧
      (n < m → Odd a → Even b → Nat.gcd (a ^ b ^ m + 1) (a ^ b ^ n + 1) = 2) ∧
      (n ≤ m → Odd b → Nat.gcd (a ^ b ^ m + 1) (a ^ b ^ n + 1) = a ^ b ^ n + 1)

/-- **Monotonicity of the number of prime factors of generalized Fermat numbers.** For natural
numbers $a$, $b$ and $n$ write $F_n(a, b) = a^{b^n} + 1$, and let $\Omega(N)$ be the number of
prime factors of $N$ counted with multiplicity. If $a, b \ge 2$ and $b$ is odd, then
$\Omega(F_n(a, b)) \le \Omega(F_m(a, b))$ for all natural numbers $n \le m$.

The source writes $\varphi_n(a, b)$ for $\Omega(F_n(a, b))$. Its open question on
$\varphi_n(2, 2)$ and its list of values of $\varphi_n(2, 2)$ are not stated here.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Corollary 1 (`integers-2026-A77-cor-1`). -/
public theorem_wanted monotone_cardFactors_pow_pow_add_one {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hbo : Odd b) :
    Monotone fun n : ℕ => ArithmeticFunction.cardFactors (a ^ b ^ n + 1)

/-- **Smaller iterated powers are not congruent to one.** Let $a, b, m \ge 2$ and $n \ge 1$ be
natural numbers with $a^{b^n} \not\equiv 1 \pmod m$. Then $a^{b^t} \not\equiv 1 \pmod m$ for every
natural number $t < n$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Lemma 2 (`integers-2026-A77-lem-2`). -/
public theorem_wanted not_pow_pow_modEq_one_of_lt {a b m n t : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hm : 2 ≤ m) (hn : 1 ≤ n) (h : ¬ a ^ b ^ n ≡ 1 [MOD m]) (ht : t < n) :
    ¬ a ^ b ^ t ≡ 1 [MOD m]

/-- **Squared prime factors of generalized Fermat numbers.** For natural numbers $a$, $b$ and $n$
write $F_n(a, b) = a^{b^n} + 1$. Let $a, b \ge 2$, let $n$ be a natural number, let $p$ be an odd
prime coprime to $ab$, and write $\operatorname{ord}_p(a)$ for the multiplicative order of $a$
modulo $p$. If $p^2$ divides $F_n(a, b)$, then $a^{p-1} \equiv 1 \pmod{p^2}$ (that is, $p$ is a
Wieferich prime to base $a$) and $\operatorname{ord}_p(a)$ divides $2b^n$. Conversely, if
$a^{p-1} \equiv 1 \pmod{p^2}$ and $\operatorname{ord}_p(a) = 2b^n$, then $p^2$ divides $F_n(a, b)$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 4 (`integers-2026-A77-thm-4`). -/
public theorem_wanted sq_dvd_pow_pow_add_one_wieferich {a b n p : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime (a * b) p) :
    (p ^ 2 ∣ a ^ b ^ n + 1 →
        a ^ (p - 1) ≡ 1 [MOD p ^ 2] ∧ orderOf (a : ZMod p) ∣ 2 * b ^ n) ∧
      (a ^ (p - 1) ≡ 1 [MOD p ^ 2] → orderOf (a : ZMod p) = 2 * b ^ n →
        p ^ 2 ∣ a ^ b ^ n + 1)

/-- **Squared prime factors of $a^{2^n} + 1$.** Let $p$ be an odd prime, let $a$ be a natural
number not divisible by $p$, and let $n$ be a natural number. Then $p^2$ divides $a^{2^n} + 1$ if
and only if $a^{p-1} \equiv 1 \pmod{p^2}$ (that is, $p$ is a Wieferich prime to base $a$) and the
multiplicative order of $a$ modulo $p$ is $2^{n+1}$.

The congruence $a^{p-1} \equiv 1 \pmod{p^2}$ is the source's equation (8) defining $p \in W(a)$.
The source assumes $a \ge 2$; for $a = 1$ both sides are false.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 5 (`integers-2026-A77-thm-5`). -/
public theorem_wanted sq_dvd_pow_two_pow_add_one_iff_wieferich {a n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpa : ¬ p ∣ a) :
    p ^ 2 ∣ a ^ 2 ^ n + 1 ↔ a ^ (p - 1) ≡ 1 [MOD p ^ 2] ∧ orderOf (a : ZMod p) = 2 ^ (n + 1)

/-- **Wieferich primes to base $a$ via multiplicative orders.** Let $p$ be a prime and $a$ a
natural number not divisible by $p$. Then $a^{p-1} \equiv 1 \pmod{p^2}$, that is, $p$ is a
Wieferich prime to base $a$, if and only if the multiplicative order of $a$ modulo $p^2$ equals
the multiplicative order of $a$ modulo $p$.

The congruence $a^{p-1} \equiv 1 \pmod{p^2}$ is the source's equation (8) defining $p \in W(a)$.
The source assumes $a \ge 2$; both sides also hold for $a = 1$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Lemma 1 (iii) (`integers-2026-A77-lem-1`). -/
public theorem_wanted pow_sub_one_modEq_one_sq_iff_orderOf_eq {a p : ℕ} (hp : p.Prime)
    (hpa : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p ^ 2] ↔ orderOf (a : ZMod (p ^ 2)) = orderOf (a : ZMod p)

/-- **Divisibility of later generalized Fermat numbers.** For natural numbers $a$, $b$ and $m$
write $F_m(a, b) = a^{b^m} + 1$. Let $a, b, D \ge 2$ and $n$ be natural numbers such that $D$
divides $F_n(a, b)$. If $b$ is odd, then $D$ divides $F_{n+k}(a, b)$ for every $k \ge 1$. If $b$
is even and $D \ge 3$, then $D$ does not divide $F_{n+k}(a, b)$ for any $k \ge 1$.

The source states the even case for $D \ge 2$; its proof gives $F_{n+k}(a, b) \equiv 2 \pmod D$,
which excludes only $D = 2$, and the even case is false there: for $a = 3$, $b = 2$, $n = 0$ and
$k = 1$, $2$ divides both $F_0(3, 2) = 4$ and $F_1(3, 2) = 10$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 7 (`integers-2026-A77-thm-7`). -/
public theorem_wanted dvd_pow_pow_add_one_shift {a b D n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hD : 2 ≤ D) (h : D ∣ a ^ b ^ n + 1) :
    (Odd b → ∀ k, 1 ≤ k → D ∣ a ^ b ^ (n + k) + 1) ∧
      (Even b → 3 ≤ D → ∀ k, 1 ≤ k → ¬ D ∣ a ^ b ^ (n + k) + 1)

/-- **Start of the period of generalized Fermat numbers modulo the square of a prime.** For
natural numbers $a$, $b$ and $k$ write $F_k(a, b) = a^{b^k} + 1$. Let $a, b \ge 2$, let $p$ be a
prime, and let $n_0$ be the least natural number with $p^2 \mid F_{n_0}(a, b)$. Say that the
sequence $(F_k(a, b))_k$ is periodic modulo $p^2$ from index $m$ if there is a $T > 0$ with
$F_{m+k+T}(a, b) \equiv F_{m+k}(a, b) \pmod{p^2}$ for every $k \ge 0$. If $b$ is odd, then $n_0$
is the least index from which the sequence is periodic modulo $p^2$; if $b$ is even, this least
index is $n_0 + 1$.

In the source's terms, $n_0$ is the index of the first term of the period when $b$ is odd, and
the index of the last term of the pre-period when $b$ is even.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Corollary 2 (`integers-2026-A77-cor-2`). -/
public theorem_wanted isLeast_periodic_start_pow_pow_add_one_mod_sq {a b p n₀ : ℕ} (ha : 2 ≤ a)
    (hb : 2 ≤ b) (hp : p.Prime) (hn₀ : p ^ 2 ∣ a ^ b ^ n₀ + 1)
    (hmin : ∀ n < n₀, ¬ p ^ 2 ∣ a ^ b ^ n + 1) :
    (Odd b → IsLeast {m : ℕ | ∃ T, 0 < T ∧
        Function.Periodic (fun k => (a ^ b ^ (m + k) + 1) % p ^ 2) T} n₀) ∧
      (Even b → IsLeast {m : ℕ | ∃ T, 0 < T ∧
        Function.Periodic (fun k => (a ^ b ^ (m + k) + 1) % p ^ 2) T} (n₀ + 1))

end

end MetaMathlibExt
