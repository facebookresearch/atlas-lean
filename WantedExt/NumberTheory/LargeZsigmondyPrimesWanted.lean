/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomic
public import MathlibExt.NumberTheory.PrimitiveDivisor

/-!
# Large Zsigmondy primes

Statements from Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62.

For integers `a`, `b` and `n ≥ 1`, `Φ_n(a, b) = b ^ φ(n) Φ_n(a / b)` is the homogenized
cyclotomic polynomial `MetaMathlibExt.homogenizedCyclotomic` (the paper's Section 3 displays
`Φ_4(a, b) = a² + b²`, `Φ_6(a, b) = a² - ab + b²`, ... and uses
`aⁿ - bⁿ = ∏_{d ∣ n} Φ_d(a, b)`).
A Zsigmondy prime for `(a, b, n)` is a primitive prime divisor of `aⁿ - bⁿ`
(`IntegerSequence.IsPrimitivePrimeDivisor`); it is large if moreover `p² ∣ aⁿ - bⁿ` or
`p > n + 1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Large Zsigmondy prime.** Let $a$, $b$, $n$ and $p$ be natural numbers. Then $p$ is a large
Zsigmondy prime for $(a, b, n)$ when $p$ is a primitive prime divisor of the term $a^n - b^n$ of
the integer sequence $(a^m - b^m)_{m \ge 0}$, that is, $n \ge 1$, $p$ is prime, $p$ divides
$a^n - b^n$ and $p$ divides no $a^m - b^m$ with $1 \le m < n$, and moreover $p^2$ divides
$a^n - b^n$ or $p > n + 1$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 1
(definition after Theorem 1). -/
def IsLargeZsigmondyPrime (a b n p : ℕ) : Prop :=
  IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p ∧
    ((p : ℤ) ^ 2 ∣ (a : ℤ) ^ n - (b : ℤ) ^ n ∨ n + 1 < p)

/-- **$7$ is a large Zsigmondy prime for $(2, 1, 3)$.** The prime $7$ is a large Zsigmondy prime
for $(a, b, n) = (2, 1, 3)$: it divides $2^3 - 1 = 7$, divides neither $2^1 - 1$ nor $2^2 - 1$,
and $7 > 3 + 1$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 1
(definition after Theorem 1). -/
theorem isLargeZsigmondyPrime_two_one_three_seven : IsLargeZsigmondyPrime 2 1 3 7 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩, Or.inr (by norm_num)⟩
  intro s hs hs3
  interval_cases s <;> norm_num

/-- **Square-root lower bound for Euler's totient.** For every positive integer $n$,
$\varphi(n) \ge \sqrt{n}/2$, where $\varphi$ is Euler's totient function.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 1
(quoted from reference [2]). -/
theorem_wanted sqrt_div_two_le_totient (n : ℕ) (hn : 0 < n) :
    Real.sqrt n / 2 ≤ (Nat.totient n : ℝ)

/-- **Homogenized cyclotomic values at $p^\beta k$.** Let $p$ be a prime, let $\beta \ge 1$ and
$k \ge 1$ be integers with $p \nmid k$, and let $a, b$ be integers; write $\Phi_m(a, b)$ for the
homogenized cyclotomic value. Then
$\Phi_{p^\beta k}(a, b) = \Phi_{pk}(a^{p^{\beta - 1}}, b^{p^{\beta - 1}})$ and
$\Phi_{p^\beta k}(a, b) \cdot \Phi_k(a^{p^{\beta - 1}}, b^{p^{\beta - 1}}) =
\Phi_k(a^{p^\beta}, b^{p^\beta})$.

The paper states the second identity as a quotient; here it is cleared of its denominator.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Corollary 1. -/
theorem_wanted homogenizedCyclotomic_prime_pow_mul {p β k : ℕ} (hp : p.Prime) (hβ : 0 < β)
    (hk : 0 < k) (hpk : ¬ p ∣ k) (a b : ℤ) :
    homogenizedCyclotomic (p ^ β * k) a b =
        homogenizedCyclotomic (p * k) (a ^ p ^ (β - 1)) (b ^ p ^ (β - 1)) ∧
      homogenizedCyclotomic (p ^ β * k) a b *
          homogenizedCyclotomic k (a ^ p ^ (β - 1)) (b ^ p ^ (β - 1)) =
        homogenizedCyclotomic k (a ^ p ^ β) (b ^ p ^ β)

/-- **Factorization of $a^n - b^n$ into homogenized cyclotomic values.** For every positive
integer $n$ and all integers $a$ and $b$,
$$a^n - b^n = \prod_{d \mid n} \Phi_d(a, b),$$
where the product runs over the positive divisors $d$ of $n$ and $\Phi_d(a, b)$ is the
homogenized cyclotomic value.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (i)
(quoted from reference [6]). -/
theorem_wanted prod_divisors_homogenizedCyclotomic {n : ℕ} (hn : 0 < n) (a b : ℤ) :
    ∏ d ∈ n.divisors, homogenizedCyclotomic d a b = a ^ n - b ^ n

/-- **Bounds for homogenized cyclotomic values.** Let $a > b$ be positive integers and let
$n \ge 1$. Then the homogenized cyclotomic value $\Phi_n(a, b)$ satisfies
$(a - b)^{\varphi(n)} \le \Phi_n(a, b) \le (a + b)^{\varphi(n)}$, where $\varphi$ is Euler's
totient function.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (ii)
(quoted from reference [6]). -/
theorem_wanted homogenizedCyclotomic_mem_Icc {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (hn : 0 < n) :
    ((a : ℤ) - b) ^ Nat.totient n ≤ homogenizedCyclotomic n a b ∧
      homogenizedCyclotomic n a b ≤ ((a : ℤ) + b) ^ Nat.totient n

/-- **Homogenized cyclotomic values at $pn$.** Let $p$ be a prime, $n$ a positive integer and
$a, b$ integers, and write $\Phi_m(a, b)$ for the homogenized cyclotomic value. If $p \mid n$,
then $\Phi_{pn}(a, b) = \Phi_n(a^p, b^p)$. If $p \nmid n$, then
$\Phi_{pn}(a, b) \cdot \Phi_n(a, b) = \Phi_n(a^p, b^p)$.

The paper states the case $p \nmid n$ as a quotient; here it is cleared of its denominator.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (iii)
(quoted from reference [6]). -/
theorem_wanted homogenizedCyclotomic_prime_mul {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (a b : ℤ) :
    (p ∣ n → homogenizedCyclotomic (p * n) a b = homogenizedCyclotomic n (a ^ p) (b ^ p)) ∧
      (¬ p ∣ n → homogenizedCyclotomic (p * n) a b * homogenizedCyclotomic n a b =
        homogenizedCyclotomic n (a ^ p) (b ^ p))

/-- **$p$-adic valuation of homogenized cyclotomic values at an odd prime.** Let $a > b$ be
positive integers, let $p$ be an odd prime dividing neither $a$ nor $b$, and let $k$ be the least
positive integer such that $p$ divides $a^k - b^k$. Write $v_p$ for the $p$-adic valuation and
$\Phi_n(a, b)$ for the homogenized cyclotomic value. Then for every positive integer $n$:
$v_p(\Phi_n(a, b)) = v_p(a^k - b^k)$ if $n = k$; $v_p(\Phi_n(a, b)) = 1$ if $n = p^\beta k$ for
some $\beta \ge 1$; and $v_p(\Phi_n(a, b)) = 0$ otherwise.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (iv)
(quoted from reference [6]). -/
theorem_wanted padicValInt_homogenizedCyclotomic_odd {a b n p k : ℕ} (hb : 0 < b)
    (hba : b < a) (hn : 0 < n) (hp : p.Prime) (hp2 : p ≠ 2) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hk : 0 < k) (hpk : (p : ℤ) ∣ (a : ℤ) ^ k - (b : ℤ) ^ k)
    (hkmin : ∀ m, 0 < m → m < k → ¬ (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m) :
    (n = k → padicValInt p (homogenizedCyclotomic n a b) =
        padicValInt p ((a : ℤ) ^ k - (b : ℤ) ^ k)) ∧
      ((∃ β, 1 ≤ β ∧ n = p ^ β * k) → padicValInt p (homogenizedCyclotomic n a b) = 1) ∧
      (n ≠ k → (¬ ∃ β, 1 ≤ β ∧ n = p ^ β * k) →
        padicValInt p (homogenizedCyclotomic n a b) = 0)

/-- **$2$-adic valuation of homogenized cyclotomic values.** Let $a > b$ be odd positive
integers. Write $v_2$ for the $2$-adic valuation and $\Phi_n(a, b)$ for the homogenized
cyclotomic value. Then for every positive integer $n$: $v_2(\Phi_n(a, b)) = v_2(a - b)$ if
$n = 1$; $v_2(\Phi_n(a, b)) = v_2(a + b)$ if $n = 2$; $v_2(\Phi_n(a, b)) = 1$ if $n = 2^\beta$
for some $\beta \ge 2$; and $v_2(\Phi_n(a, b)) = 0$ if $n$ is not a power of $2$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (v)
(quoted from reference [6]). -/
theorem_wanted padicValInt_two_homogenizedCyclotomic {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (ha : Odd a) (hb' : Odd b) (hn : 0 < n) :
    (n = 1 → padicValInt 2 (homogenizedCyclotomic n a b) = padicValInt 2 ((a : ℤ) - b)) ∧
      (n = 2 → padicValInt 2 (homogenizedCyclotomic n a b) = padicValInt 2 ((a : ℤ) + b)) ∧
      ((∃ β, 2 ≤ β ∧ n = 2 ^ β) → padicValInt 2 (homogenizedCyclotomic n a b) = 1) ∧
      ((¬ ∃ β, n = 2 ^ β) → padicValInt 2 (homogenizedCyclotomic n a b) = 0)

/-- **Prime divisors of homogenized cyclotomic values.** Let $a > b$ be coprime positive
integers, let $n \ge 2$, let $\Phi_n(a, b)$ be the homogenized cyclotomic value, let $p$ be a
prime dividing $\Phi_n(a, b)$, and let $k$ be the least positive integer such that $p$ divides
$a^k - b^k$. Then one of the following holds: (i) $p = 2$ and $n = 2^\beta$ for some
$\beta \ge 1$; (ii) $p \ge 3$, $n = k$, and $p$ is a primitive prime divisor of the term
$a^n - b^n$ of the sequence $(a^m - b^m)_{m \ge 0}$; (iii) $p$ is the greatest prime factor of
$n$, $p > 2$, $n = p^\beta k$ for some $\beta \ge 1$, and the $p$-adic valuation of
$\Phi_n(a, b)$ is $1$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 4. -/
theorem_wanted prime_dvd_homogenizedCyclotomic_cases {a b n p k : ℕ} (hb : 0 < b)
    (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) (hp : p.Prime)
    (hpΦ : (p : ℤ) ∣ homogenizedCyclotomic n a b) (hk : 0 < k)
    (hpk : (p : ℤ) ∣ (a : ℤ) ^ k - (b : ℤ) ^ k)
    (hkmin : ∀ m, 0 < m → m < k → ¬ (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m) :
    (p = 2 ∧ ∃ β, 1 ≤ β ∧ n = 2 ^ β) ∨
      (3 ≤ p ∧ n = k ∧
        IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p) ∨
      (p ∈ n.primeFactors ∧ (∀ r ∈ n.primeFactors, r ≤ p) ∧ 2 < p ∧
        (∃ β, 1 ≤ β ∧ n = p ^ β * k) ∧ padicValInt p (homogenizedCyclotomic n a b) = 1)

/-- **Zsigmondy primes divide the homogenized cyclotomic value.** Let $a$ and $b$ be distinct
coprime positive integers and let $n \ge 2$. If $p$ is a primitive prime divisor of the term
$a^n - b^n$ of the integer sequence $(a^m - b^m)_{m \ge 0}$ (a Zsigmondy prime for $(a, b, n)$),
then $p$ divides the homogenized cyclotomic value $\Phi_n(a, b)$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 5. -/
theorem_wanted dvd_homogenizedCyclotomic_of_isPrimitivePrimeDivisor {a b n p : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (hcop : a.Coprime b) (hn : 2 ≤ n)
    (hp : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p) :
    (p : ℤ) ∣ homogenizedCyclotomic n a b

/-- **A Zsigmondy prime $q$ that is not large satisfies $n = q - 1$.** Let $a > b$ be coprime
positive integers and let $n \ge 2$. If $q$ is a primitive prime divisor of the term $a^n - b^n$
of the integer sequence $(a^m - b^m)_{m \ge 0}$ and $q$ is not a large Zsigmondy prime for
$(a, b, n)$, then $n = q - 1$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 6. -/
theorem_wanted eq_sub_one_of_not_isLargeZsigmondyPrime {a b n q : ℕ} (hb : 0 < b)
    (hba : b < a) (hcop : a.Coprime b) (hn : 2 ≤ n)
    (hq : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q)
    (hql : ¬ IsLargeZsigmondyPrime a b n q) :
    n = q - 1

/-- **A size criterion for a large Zsigmondy prime.** Let $a$ and $b$ be distinct coprime
positive integers and let $n \ge 3$. If $(n + 1) q < \Phi_n(a, b)$ for every prime factor $q$ of
$n$, where $\Phi_n(a, b)$ is the homogenized cyclotomic value, then there is a large Zsigmondy
prime for $(a, b, n)$.

Equivalently, the hypothesis asks that $n + 1$ times the greatest prime factor of $n$ be less
than $\Phi_n(a, b)$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 7. -/
theorem_wanted exists_isLargeZsigmondyPrime_of_lt {a b n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (hcop : a.Coprime b) (hn : 3 ≤ n)
    (hlt : ∀ q ∈ n.primeFactors, ((n + 1) * q : ℤ) < homogenizedCyclotomic n a b) :
    ∃ p, IsLargeZsigmondyPrime a b n p

/-- **Large Zsigmondy primes for exponents $n > 1$ outside six values.** Let $a > b$ be coprime
positive integers and let $n > 1$ with $n \notin \{2, 4, 6, 10, 12, 18\}$. Then there is a
large Zsigmondy prime for $(a, b, n)$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 8. -/
theorem_wanted exists_isLargeZsigmondyPrime_of_not_mem {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (hcop : a.Coprime b) (hn : 1 < n) (hn' : n ∉ ({2, 4, 6, 10, 12, 18} : Finset ℕ)) :
    ∃ p, IsLargeZsigmondyPrime a b n p

/-- **Avcı's classification of large Zsigmondy primes.** Let $a > b$ be coprime positive
integers and let $n > 1$. There is a large Zsigmondy prime for $(a, b, n)$ if and only if none
of the following holds: $n = 2$ and $a + b = 2^s$ or $a + b = 3 \cdot 2^s$ for some natural
number $s$; $n = 4$ and $(a, b) \in \{(2, 1), (3, 1)\}$; $n = 6$ and
$(a, b) \in \{(2, 1), (3, 1), (3, 2), (5, 1), (5, 4)\}$; $n = 10$ and
$(a, b) \in \{(2, 1), (3, 2)\}$; $n = 12$ and $(a, b) = (2, 1)$; $n = 18$ and $(a, b) = (2, 1)$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Theorem 1
(the converse is the classification in the proof of Theorem 1). -/
theorem_wanted exists_isLargeZsigmondyPrime_iff {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (hcop : a.Coprime b) (hn : 1 < n) :
    (∃ p, IsLargeZsigmondyPrime a b n p) ↔
      ¬ ((n = 2 ∧ ∃ s : ℕ, a + b = 2 ^ s ∨ a + b = 3 * 2 ^ s) ∨
        (n = 4 ∧ (a, b) ∈ ({(2, 1), (3, 1)} : Finset (ℕ × ℕ))) ∨
        (n = 6 ∧ (a, b) ∈ ({(2, 1), (3, 1), (3, 2), (5, 1), (5, 4)} : Finset (ℕ × ℕ))) ∨
        (n = 10 ∧ (a, b) ∈ ({(2, 1), (3, 2)} : Finset (ℕ × ℕ))) ∨
        (n = 12 ∧ (a, b) = (2, 1)) ∨ (n = 18 ∧ (a, b) = (2, 1)))

end

end MetaMathlibExt
