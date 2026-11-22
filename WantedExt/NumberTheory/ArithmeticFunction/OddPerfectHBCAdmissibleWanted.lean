/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.Divisors

namespace MetaMathlibExt

@[expose] public section

/-- **Comparison of products of $1 - 1/x$ under prefix-product domination.** Let $k \ge 0$ and let
$z_1 \le \dots \le z_k$ and $y_1 \le \dots \le y_k$ be real numbers, all greater than $1$, such
that $z_1 \cdots z_l \le y_1 \cdots y_l$ for every $l$ with $0 \le l \le k$ (for $l = 0$ both sides
are the empty product). Then $\prod_{i=1}^k (1 - 1/z_i) \le \prod_{i=1}^k (1 - 1/y_i)$, with
equality if and only if $z_i = y_i$ for all $i$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 2 (`integers-2024-A114-lem-2`), citing its reference [4]. -/
public theorem_wanted prod_one_sub_inv_le_of_prefix_prod_le (k : ℕ) (z y : Fin k → ℝ)
    (hz : Monotone z) (hy : Monotone y) (hz1 : ∀ i, 1 < z i) (hy1 : ∀ i, 1 < y i)
    (hprefix : ∀ l ≤ k, ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < l), z i ≤
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < l), y i) :
    ∏ i, (1 - 1 / z i) ≤ ∏ i, (1 - 1 / y i) ∧
      (∏ i, (1 - 1 / z i) = ∏ i, (1 - 1 / y i) ↔ z = y)

/-- **First-element bounds for HBC-admissible tuples at $1/2$.** Let $k \ge 1$ and let
$y_1 < y_2 < \dots < y_k$ be positive integers with
$\prod_{i=1}^{k} (1 - 1/y_i) \le 1/2 < \prod_{i=1}^{k-1} (1 - 1/y_i)$. Then $y_1 \le k + 1$; if
every $y_i$ is odd, then $y_1 < 2(k + 3)/3$; and if every $y_i$ is prime, then $y_1 < 3k/7 + 3$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 5 (`integers-2024-A114-lem-5`). -/
public theorem_wanted hbcAdmissible_half_first_le (k : ℕ) (hk : 0 < k) (y : Fin k → ℕ)
    (hmono : StrictMono y) (hpos : ∀ i, 0 < y i)
    (hle : ∏ i, (1 - 1 / (y i : ℚ)) ≤ 1 / 2)
    (hlt : 1 / 2 < ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < k - 1),
      (1 - 1 / (y i : ℚ))) :
    y ⟨0, hk⟩ ≤ k + 1 ∧
      ((∀ i, Odd (y i)) → (y ⟨0, hk⟩ : ℚ) < 2 * (k + 3) / 3) ∧
      ((∀ i, (y i).Prime) → (y ⟨0, hk⟩ : ℚ) < 3 * k / 7 + 3)

/-- **A linear bound on the smallest prime divisor of an odd perfect number.** If $N$ is an odd
perfect number with $m$ distinct prime divisors, then the smallest prime divisor $p_1$ of $N$
satisfies $p_1 < 3m/7 + 3$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 6 (`integers-2024-A114-lem-6`). -/
public theorem_wanted oddPerfect_minFac_lt (N : ℕ) (hodd : Odd N) (hperf : N.Perfect) :
    (N.minFac : ℚ) < 3 * N.primeFactors.card / 7 + 3

/-- **Sylvester's bound on the number of prime divisors of an odd perfect number.** Every odd
perfect number has at least five distinct prime divisors.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (ii) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_five_le_card_primeFactors (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) : 5 ≤ N.primeFactors.card

/-- **Dickson's finiteness theorem for odd perfect numbers.** For every natural number $m$, there
are only finitely many odd perfect numbers with exactly $m$ distinct prime divisors.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (iii) (`integers-2024-A114-lem-1`). -/
public theorem_wanted finite_setOf_oddPerfect_card_primeFactors_eq (m : ℕ) :
    {N : ℕ | Odd N ∧ N.Perfect ∧ N.primeFactors.card = m}.Finite

/-- **Steuerwald's theorem on odd perfect numbers.** If $N$ is an odd perfect number, then $N$ has
a prime divisor whose exponent in the prime factorization of $N$ is even and different from $2$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (iv) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_exists_even_factorization_ne_two (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ N.factorization p ≠ 2

/-- **McDaniel's exponent bound for odd perfect numbers below $10^{9118}$.** If $N$ is an odd
perfect number with $N < 10^{9118}$, then $N$ has a prime divisor whose exponent in the prime
factorization of $N$ is at least $6$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (v) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_exists_six_le_factorization_of_lt (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) (hN : N < 10 ^ 9118) :
    ∃ p ∈ N.primeFactors, 6 ≤ N.factorization p

/-- **Odd perfect numbers not divisible by three have at least eleven prime divisors.** Every odd
perfect number that is not divisible by $3$ has at least $11$ distinct prime divisors. This is due
to Kishore (1981) and Hagis (1983).

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (vi) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_eleven_le_card_primeFactors_of_not_three_dvd (N : ℕ)
    (hodd : Odd N) (hperf : N.Perfect) (h3 : ¬ 3 ∣ N) : 11 ≤ N.primeFactors.card

/-- **Nielsen's bound on the number of prime divisors of an odd perfect number.** Every odd perfect
number $N$ has at least ten distinct prime divisors, and at least twelve if $3$ does not divide $N$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (vii) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_ten_le_card_primeFactors (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) :
    10 ≤ N.primeFactors.card ∧ (¬ 3 ∣ N → 12 ≤ N.primeFactors.card)

/-- **Zelinsky's bound on the smallest prime divisor of an odd perfect number.** If $N$ is an odd
perfect number with $m$ distinct prime divisors, then the smallest prime divisor $p$ of $N$
satisfies $p < (m - 1)/2$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (viii) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_minFac_lt_card_sub_one_div_two (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) :
    (N.minFac : ℚ) < ((N.primeFactors.card : ℚ) - 1) / 2

/-- **Ochem–Rao lower bound for odd perfect numbers.** Every odd perfect number exceeds $10^{1500}$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (ix) (`integers-2024-A114-lem-1`). -/
public theorem_wanted ten_pow_fifteen_hundred_lt_of_oddPerfect (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) : 10 ^ 1500 < N

/-- **Goto–Ohno–Iannucci bounds on the largest prime divisors of an odd perfect number.** If $N$ is
an odd perfect number, then $N$ has three distinct prime divisors $p$, $q$, $r$ with
$p \ge 10^8$, $q \ge 10^4$ and $r \ge 100$. Equivalently, the largest, second largest and third
largest prime divisors of $N$ are at least $10^8$, $10^4$ and $100$ respectively.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (x) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_exists_three_large_prime_divisors (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) :
    ∃ p ∈ N.primeFactors, ∃ q ∈ N.primeFactors, ∃ r ∈ N.primeFactors,
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ 10 ^ 8 ≤ p ∧ 10 ^ 4 ≤ q ∧ 100 ≤ r

/-- **Product identities for calibrating numbers.** Let $a$ and $d$ be positive integers and let
$k \ge 1$. Put $\alpha = (a + d)/d$, and let $n_i = 1 + \alpha^{2^{i-1}}$ for $1 \le i < k$ and
$n_k = \alpha^{2^{k-1}}$ (the calibrating numbers for $a/(a + d)$). Then
$\prod_{i=1}^{k} (1 - 1/n_i) = a/(a + d)$; for every $j$ with $1 \le j < k$,
$\prod_{i=1}^{j} n_i = (d/a)(\alpha^{2^j} - 1)$; and
$\prod_{i=1}^{k} n_i = (d/a)(\alpha^{2^k} - \alpha^{2^{k-1}})$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 3. -/
public theorem_wanted hbcCalibrating_prod_identities (a d k : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hk : 1 ≤ k) :
    let α : ℚ := (a + d) / d
    let n : ℕ → ℚ := fun i => if i < k then 1 + α ^ 2 ^ (i - 1) else α ^ 2 ^ (k - 1)
    ∏ i ∈ Finset.Icc 1 k, (1 - 1 / n i) = (a : ℚ) / (a + d) ∧
      (∀ j, 1 ≤ j → j < k → ∏ i ∈ Finset.Icc 1 j, n i = (d / a) * (α ^ 2 ^ j - 1)) ∧
      ∏ i ∈ Finset.Icc 1 k, n i = (d / a) * (α ^ 2 ^ k - α ^ 2 ^ (k - 1))

/-- **Stone's product bound for HBC-admissible tuples.** Let $a$ and $d$ be coprime positive
integers, let $k \ge 1$, and let $y_1 < y_2 < \dots < y_k$ be positive integers with
$\prod_{i=1}^{k} (1 - 1/y_i) \le a/(a + d) < \prod_{i=1}^{k-1} (1 - 1/y_i)$ (the source calls such
a tuple HBC-admissible for $a/(a + d)$). Put $\alpha = (a + d)/d$, let $n_i = 1 + \alpha^{2^{i-1}}$
for $1 \le i < k$ and $n_k = \alpha^{2^{k-1}}$, and let $F_k(x) = x^{2^k} - x^{2^{k-1}}$. Then some
$\kappa$ with $1 \le \kappa \le k$ has $\prod_{i=1}^{\kappa} y_i \le \prod_{i=1}^{\kappa} n_i$.
Moreover, let $\kappa$ with $1 \le \kappa \le k$ satisfy this inequality while every $\kappa'$ with
$\kappa < \kappa' \le k$ satisfies $\prod_{i=1}^{\kappa'} n_i < \prod_{i=1}^{\kappa'} y_i$, so that
$\kappa$ is the largest such index. If $\kappa < k$, then
$a \prod_{i=1}^{k} y_i \le F_k(\alpha d^{1/2^{\kappa}})$; if $\kappa = k$, then
$a \prod_{i=1}^{k} y_i \le d \, F_k(\alpha)$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Theorem 1. -/
public theorem_wanted hbcAdmissible_exists_prefix_le_and_prod_le (a d k : ℕ) (ha : 0 < a)
    (hd : 0 < d) (hcop : Nat.Coprime a d) (hk : 1 ≤ k) (y : ℕ → ℕ) (hy0 : 0 < y 1) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ (a : ℝ) / (a + d))
    (hlt : (a : ℝ) / (a + d) < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ))) :
    let α : ℝ := (a + d) / d
    let n : ℕ → ℝ := fun i => if i < k then 1 + α ^ 2 ^ (i - 1) else α ^ 2 ^ (k - 1)
    let ακ : ℕ → ℝ := fun κ => if κ < k then α * (d : ℝ) ^ ((1 : ℝ) / 2 ^ κ) else α
    (∃ κ ∈ Finset.Icc 1 k, ∏ i ∈ Finset.Icc 1 κ, (y i : ℝ) ≤ ∏ i ∈ Finset.Icc 1 κ, n i) ∧
      ∀ κ ∈ Finset.Icc 1 k, ∏ i ∈ Finset.Icc 1 κ, (y i : ℝ) ≤ ∏ i ∈ Finset.Icc 1 κ, n i →
        (∀ κ' ∈ Finset.Icc 1 k, κ < κ' →
          ∏ i ∈ Finset.Icc 1 κ', n i < ∏ i ∈ Finset.Icc 1 κ', (y i : ℝ)) →
        a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
          (if κ = k then (d : ℝ) else 1) * (ακ κ ^ 2 ^ k - ακ κ ^ 2 ^ (k - 1))

/-- **Stone's $\sqrt{d}$ product bound for HBC-admissible tuples.** Let $a$ and $d$ be coprime
positive integers, let $k \ge 1$, and let $y_1 < y_2 < \dots < y_k$ be positive integers with
$\prod_{i=1}^{k} (1 - 1/y_i) \le a/(a + d) < \prod_{i=1}^{k-1} (1 - 1/y_i)$. Put
$\beta = (a + d)/\sqrt{d}$. Then $a \prod_{i=1}^{k} y_i \le \beta^{2^k} - \beta^{2^{k-1}}$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Corollary 1. -/
public theorem_wanted hbcAdmissible_prod_le_sqrt (a d k : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcop : Nat.Coprime a d) (hk : 1 ≤ k) (y : ℕ → ℕ) (hy0 : 0 < y 1) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ (a : ℝ) / (a + d))
    (hlt : (a : ℝ) / (a + d) < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ))) :
    a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      ((a + d) / Real.sqrt d) ^ 2 ^ k - ((a + d) / Real.sqrt d) ^ 2 ^ (k - 1)

/-- **Stone's $d^{3/4}$ product bound for HBC-admissible tuples.** Let $a$ and $d$ be coprime
positive integers, let $k \ge 2$, and let $y_1 < y_2 < \dots < y_k$ be positive integers with
$\prod_{i=1}^{k} (1 - 1/y_i) \le a/(a + d) < \prod_{i=1}^{k-1} (1 - 1/y_i)$ and
$y_1 \ne \lfloor 1 + (a + d)/d \rfloor$. Put $\beta = (a + d)/d^{3/4}$. Then
$a \prod_{i=1}^{k} y_i \le \beta^{2^k} - \beta^{2^{k-1}}$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Corollary 2. -/
public theorem_wanted hbcAdmissible_prod_le_of_ne_floor (a d k : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcop : Nat.Coprime a d) (hk : 2 ≤ k) (y : ℕ → ℕ) (hy0 : 0 < y 1) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ (a : ℝ) / (a + d))
    (hlt : (a : ℝ) / (a + d) < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ)))
    (hy1 : y 1 ≠ ⌊1 + ((a : ℝ) + d) / d⌋₊) :
    a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      ((a + d) / (d : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 ^ k - ((a + d) / (d : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 ^ (k - 1)

/-- **Product bound for HBC-admissible tuples at $7/10$.** Let $k \ge 3$ and let
$y_1 < y_2 < \dots < y_k$ be positive integers with
$\prod_{i=1}^{k} (1 - 1/y_i) \le 7/10 < \prod_{i=1}^{k-1} (1 - 1/y_i)$. Then
$\prod_{i=1}^{k} y_i \le \frac{2}{7}\bigl(\sqrt{15}^{\,2^k} - \sqrt{15}^{\,2^{k-1}}\bigr)$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 4. -/
public theorem_wanted hbcAdmissible_seven_tenths_prod_le (k : ℕ) (hk : 3 ≤ k) (y : ℕ → ℕ) (hy0 : 0 < y 1) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ 7 / 10)
    (hlt : 7 / 10 < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ))) :
    ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      2 / 7 * (Real.sqrt 15 ^ 2 ^ k - Real.sqrt 15 ^ 2 ^ (k - 1))

/-- **Product bounds for prime tuples at $1/2$ by size of the first prime.** Let
$p_1 < p_2 < \dots < p_k$ be primes with
$\prod_{i=1}^{k} (1 - 1/p_i) \le 1/2 < \prod_{i=1}^{k-1} (1 - 1/p_i)$ and $p_1 \ge 5$, and let
$F_k(x) = x^{2^k} - x^{2^{k-1}}$ and $P = \prod_{i=1}^{k} p_i$. Then $P \le F_k(\sqrt{8/3^{7/8}})$.
Moreover, if $6 \le p_1 < 18$, then $P \le F_k(\sqrt{12/5^{15/16}})$; if $18 \le p_1 < 258$, then
$P \le F_k(\sqrt{512/255^{31/32}})$; and if $p_1 \ge 258$, then
$P \le F_k\bigl(\sqrt{2^{5/4} (2^{16} + 1)/2^{16}}\bigr)$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 7. -/
public theorem_wanted hbcAdmissible_half_prime_prod_le_of_five_le (k : ℕ) (y : ℕ → ℕ) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hprime : ∀ i ∈ Finset.Icc 1 k, (y i).Prime)
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ 1 / 2)
    (hlt : 1 / 2 < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ)))
    (h5 : 5 ≤ y 1) :
    let F : ℝ → ℝ := fun x => x ^ 2 ^ k - x ^ 2 ^ (k - 1)
    ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤ F (Real.sqrt (8 / (3 : ℝ) ^ ((7 : ℝ) / 8))) ∧
      (6 ≤ y 1 → y 1 < 18 →
        ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤ F (Real.sqrt (12 / (5 : ℝ) ^ ((15 : ℝ) / 16)))) ∧
      (18 ≤ y 1 → y 1 < 258 →
        ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤ F (Real.sqrt (512 / (255 : ℝ) ^ ((31 : ℝ) / 32)))) ∧
      (258 ≤ y 1 →
        ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
          F (Real.sqrt ((2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16)))

/-- **Product bound for prime tuples at $1/2$ starting at $5$.** Let $p_1 < p_2 < \dots < p_k$ be
primes with $\prod_{i=1}^{k} (1 - 1/p_i) \le 1/2 < \prod_{i=1}^{k-1} (1 - 1/p_i)$ and $p_1 = 5$.
Put $x = \sqrt{8/3^{31/32}}$. Then $\prod_{i=1}^{k} p_i \le x^{2^k} - x^{2^{k-1}}$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 8. -/
public theorem_wanted hbcAdmissible_half_prime_prod_le_of_eq_five (k : ℕ) (y : ℕ → ℕ) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hprime : ∀ i ∈ Finset.Icc 1 k, (y i).Prime)
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ 1 / 2)
    (hlt : 1 / 2 < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ)))
    (h5 : y 1 = 5) :
    ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      Real.sqrt (8 / (3 : ℝ) ^ ((31 : ℝ) / 32)) ^ 2 ^ k -
        Real.sqrt (8 / (3 : ℝ) ^ ((31 : ℝ) / 32)) ^ 2 ^ (k - 1)

end

end MetaMathlibExt
