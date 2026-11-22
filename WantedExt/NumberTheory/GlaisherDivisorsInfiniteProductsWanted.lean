/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Expand
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition

/-!
# Glaisher's divisors and infinite products: wishlist

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6.

The *series-divisor* `(σ^A(k))_{k ≥ 1}` of a formal power series `A(q) = ∑ a(k) q^k`
is defined in the paper (Definition 1) by `n a(n) = ∑_{i=1}^n σ^A(i) a(n-i)` for
`n ≥ 1`, with `σ^A(r) = 0` unless `r` is a positive integer. No new definition is
introduced: each statement takes a sequence `s` together with that recurrence as a
hypothesis. Glaisher's divisor functions `d_A, …, d_G` and `σ̄₃`, `σ̃₃` are the divisor
sums displayed in the paper's introduction; they are written inline below (local
notation), with the paper's convention `σ(r) = 0` unless `r` is a positive integer.
Infinite sums over `j` are truncated at a bound past which every term vanishes.
-/

open PowerSeries
open scoped ArithmeticFunction.sigma

namespace MetaMathlibExt

@[expose] public section

/-- `σ(m)` as an integer. -/
local notation "σ₁" m:max => ((σ 1 m : ℕ) : ℤ)
/-- `σ(m / k)`, which is `0` unless `k ∣ m`. -/
local notation "σdiv" k:max m:max => (if k ∣ m then ((σ 1 (m / k) : ℕ) : ℤ) else 0)
/-- `d_B(m)`: sum of the odd divisors of `m`. -/
local notation "dB" m:max => ∑ d ∈ Nat.divisors m with Odd d, (d : ℤ)
/-- `d_C(m)`: sum of the even divisors of `m`. -/
local notation "dC" m:max => ∑ d ∈ Nat.divisors m with Even d, (d : ℤ)
/-- `d_D(m)`: sum of the divisors `d` of `m` with `m / d` odd. -/
local notation "dD" m:max => ∑ d ∈ Nat.divisors m with Odd (m / d), (d : ℤ)
/-- `d_E(m)`: sum of the divisors `d` of `m` with `m / d` even. -/
local notation "dE" m:max => ∑ d ∈ Nat.divisors m with Even (m / d), (d : ℤ)
/-- `d_F(m) = ∑_{d ∣ m} (-1)^(d-1) d`. -/
local notation "dF" m:max => ∑ d ∈ Nat.divisors m, (-1 : ℤ) ^ (d - 1) * (d : ℤ)
/-- `d_G(m) = ∑_{d ∣ m} (-1)^(m/d-1) d`. -/
local notation "dG" m:max => ∑ d ∈ Nat.divisors m, (-1 : ℤ) ^ (m / d - 1) * (d : ℤ)
/-- `σ̄₃(m) = ∑_{d ∣ m, m/d odd} d³`. -/
local notation "σbar₃" m:max => ∑ d ∈ Nat.divisors m with Odd (m / d), (d : ℤ) ^ 3
/-- `σ̃₃(m) = ∑_{d ∣ m} (-1)^(d-1) d³`. -/
local notation "σtilde₃" m:max => ∑ d ∈ Nat.divisors m, (-1 : ℤ) ^ (d - 1) * (d : ℤ) ^ 3
/-- `p(m)`, the number of partitions of `m`. -/
local notation "pp" m:max => ((Fintype.card (Nat.Partition m) : ℕ) : ℤ)
/-- `p_o(m)`, the number of partitions of `m` into odd parts. -/
local notation "po" m:max => ((Finset.card (Nat.Partition.odds m) : ℕ) : ℤ)
/-- `p_d(m)`, the number of partitions of `m` into distinct parts. -/
local notation "pd" m:max => ((Finset.card (Nat.Partition.distincts m) : ℕ) : ℤ)
set_option quotPrecheck false in
/-- `p_e(m)`, the number of partitions of `m` into even parts. -/
local notation "pe" m:max =>
  ((Finset.card (Finset.filter (fun π : Nat.Partition m => ∀ i ∈ π.parts, Even i)
    Finset.univ) : ℕ) : ℤ)
/-- `p̄(m)`, the number of overpartitions of `m`. -/
local notation "pbar" m:max => ((Nat.card (Nat.Overpartition m) : ℕ) : ℤ)
set_option quotPrecheck false in
/-- `r_k(m)`: ordered representations of `m` as a sum of `k` squares of integers. -/
local notation "rsq" k:max m:max =>
  ((Set.ncard {x : Fin k → ℤ | ∑ i, x i ^ 2 = ((m : ℕ) : ℤ)} : ℕ) : ℤ)
set_option quotPrecheck false in
/-- `t_k(m)`: ordered representations of `m` as a sum of `k` triangular numbers. -/
local notation "ttri" k:max m:max =>
  ((Set.ncard {x : Fin k → ℕ | ∑ i, x i * (x i + 1) / 2 = m} : ℕ) : ℤ)

/-- **Series-divisors add under multiplication.** Let $R$ be a commutative ring and let $A$, $B$
be formal power series over $R$ with coefficients $a(n)$, $b(n)$. Suppose $s_A, s_B$ are maps
$\mathbb{N} \to R$ with $n\,a(n) = \sum_{i=1}^{n} s_A(i)\,a(n-i)$ and
$n\,b(n) = \sum_{i=1}^{n} s_B(i)\,b(n-i)$ for every $n \ge 0$ (that is, $s_A$ and $s_B$ are
series-divisors of $A$ and $B$). Then, writing $c(n)$ for the coefficients of $AB$,
$n\,c(n) = \sum_{i=1}^{n} \bigl(s_A(i) + s_B(i)\bigr)\,c(n-i)$ for every $n \ge 0$, so $s_A + s_B$
is a series-divisor of $AB$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 2
(`jis-2024-24.1.6-lem-2`). -/
public theorem_wanted series_divisor_add_of_mul {R : Type*} [CommRing R]
    (A B : PowerSeries R) (sA sB : ℕ → R)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, sA i * coeff (n - i) A)
    (hB : ∀ n : ℕ, (n : R) * coeff n B = ∑ i ∈ Finset.Icc 1 n, sB i * coeff (n - i) B) :
    ∀ n : ℕ, (n : R) * coeff n (A * B) =
      ∑ i ∈ Finset.Icc 1 n, (sA i + sB i) * coeff (n - i) (A * B)

/-- **Calculus of series-divisors.** Let $R$ be a commutative ring, let $A$ be a formal power
series over $R$, write $[q^k]F$ for the coefficient of $q^k$ in a power series $F$, and let
$s : \mathbb{N} \to R$ satisfy $n\,[q^n]A = \sum_{i=1}^{n} s(i)\,[q^{n-i}]A$ for every $n \ge 0$
(that is, $s$ is a series-divisor of $A$). Then the following hold for every $n \ge 0$:
(a) for every power series $B$ over $R$ with $AB = 1$,
$n\,[q^n]B = \sum_{i=1}^{n} \bigl(-s(i)\bigr)\,[q^{n-i}]B$;
(b) $n\,[q^n]A(-q) = \sum_{i=1}^{n} (-1)^i s(i)\,[q^{n-i}]A(-q)$;
(c) for every integer $m \ge 1$, $n\,[q^n]A(q^m) = \sum_{i=1}^{n} t_m(i)\,[q^{n-i}]A(q^m)$,
where $t_m(i) = m\,s(i/m)$ if $m \mid i$ and $t_m(i) = 0$ otherwise;
(d) for every integer $m \ge 0$, $n\,[q^n]A^m = \sum_{i=1}^{n} m\,s(i)\,[q^{n-i}]A^m$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Proposition 3
(`jis-2024-24.1.6-prop-3`). -/
public theorem_wanted series_divisor_calculus {R : Type*} [CommRing R]
    (A : PowerSeries R) (s : ℕ → R)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) A) :
    (∀ B : PowerSeries R, A * B = 1 → ∀ n : ℕ,
      (n : R) * coeff n B = ∑ i ∈ Finset.Icc 1 n, -s i * coeff (n - i) B) ∧
    (∀ n : ℕ, (n : R) * coeff n (rescale (-1) A) =
      ∑ i ∈ Finset.Icc 1 n, (-1) ^ i * s i * coeff (n - i) (rescale (-1) A)) ∧
    (∀ (m : ℕ) (hm : m ≠ 0) (n : ℕ), (n : R) * coeff n (expand m hm A) =
      ∑ i ∈ Finset.Icc 1 n,
        (if m ∣ i then (m : R) * s (i / m) else 0) * coeff (n - i) (expand m hm A)) ∧
    (∀ m n : ℕ, (n : R) * coeff n (A ^ m) =
      ∑ i ∈ Finset.Icc 1 n, (m : R) * s i * coeff (n - i) (A ^ m))

/-- **Coefficient recursion for powers of a power series.** Let $R$ be a commutative ring, let
$A$ be a formal power series over $R$ with coefficients $a(k)$, and let $s : \mathbb{N} \to R$
satisfy $k\,a(k) = \sum_{i=1}^{k} s(i)\,a(k-i)$ for every $k \ge 0$ (that is, $s$ is a
series-divisor of $A$). For natural numbers $m$ and $k$, write $a_m(k)$ for the coefficient of
$q^k$ in $A^m$. Then for all natural numbers $m$ and $n$,
$n\,a_m(n) = m \sum_{j=1}^{n} s(j)\,a_m(n-j)$.

Source: in Corollary 4 the printed summand `σ^A(i)` is read as `σ^A(j)` (the summation index).

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Corollary 4
(`jis-2024-24.1.6-cor-4`). -/
public theorem_wanted series_divisor_pow_recursion {R : Type*} [CommRing R]
    (A : PowerSeries R) (s : ℕ → R)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) A)
    (m n : ℕ) :
    (n : R) * coeff n (A ^ m) = (m : R) * ∑ j ∈ Finset.Icc 1 n, s j * coeff (n - j) (A ^ m)

/-- **Glaisher's divisor functions as series-divisors.** Let $n$ be a natural number. For a
positive integer $m$, write $\sigma(m)$ for the sum of the divisors of $m$, $d_B(m)$ and
$d_C(m)$ for the sums of the odd and of the even divisors of $m$, $d_D(m)$ and $d_E(m)$ for the
sums of the divisors $d$ of $m$ with $m/d$ odd and with $m/d$ even,
$d_F(m) = \sum_{d \mid m} (-1)^{d-1} d$ and $d_G(m) = \sum_{d \mid m} (-1)^{m/d-1} d$, and set all
of these to $0$ at $m = 0$. Let $p(m)$, $p_o(m)$, $p_e(m)$ and $p_d(m)$ be the numbers of
partitions of $m$, of partitions of $m$ into odd parts, into even parts and into distinct parts,
let $\bar p(m)$ be the number of overpartitions of $m$, let $r(m)$ be the number of integers $k$
with $k^2 = m$, and let $t(m)$ be the number of natural numbers $k$ with $k(k+1)/2 = m$. Then
$d_C(n) = 2 d_E(n)$, and, with every sum running over $1 \le i \le n$,
$n\,p(n) = \sum_i \sigma(i)\,p(n-i)$, $n\,p_o(n) = \sum_i d_B(i)\,p_o(n-i)$,
$n\,p_e(n) = \sum_i d_C(i)\,p_e(n-i)$, $n\,\bar p(n) = \sum_i 2 d_D(i)\,\bar p(n-i)$,
$n\,r(n) = \sum_i (-1)^{i+1} 2 d_D(i)\,r(n-i)$, $n\,t(n) = \sum_i d_F(i)\,t(n-i)$ and
$n\,p_d(n) = \sum_i d_G(i)\,p_d(n-i)$.

In the language of the source, these recurrences say that $\sigma$, $d_B$, $d_C$, $2 d_D$,
$i \mapsto (-1)^{i+1} 2 d_D(i)$, $d_F$ and $d_G$ are the series-divisors of the generating
functions of $p$, $p_o$, $p_e$, $\bar p$, $\varphi(q) = \sum_{k \in \mathbb{Z}} q^{k^2}$,
$\psi(q) = \sum_{k \ge 0} q^{k(k+1)/2}$ and $p_d$ respectively.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 9
(`jis-2024-24.1.6-thm-9`). -/
public theorem_wanted glaisher_divisors_series_divisor_recurrences (n : ℕ) :
    (n : ℤ) * pp n = ∑ i ∈ Finset.Icc 1 n, (σ₁ i) * pp (n - i) ∧
    (n : ℤ) * po n = ∑ i ∈ Finset.Icc 1 n, (dB i) * po (n - i) ∧
    (dC n) = 2 * dE n ∧
    (n : ℤ) * pe n = ∑ i ∈ Finset.Icc 1 n, (dC i) * pe (n - i) ∧
    (n : ℤ) * pbar n = ∑ i ∈ Finset.Icc 1 n, 2 * (dD i) * pbar (n - i) ∧
    (n : ℤ) * ((Set.ncard {k : ℤ | k ^ 2 = (n : ℤ)} : ℕ) : ℤ) =
      ∑ i ∈ Finset.Icc 1 n, (-1) ^ (i + 1) * 2 * (dD i) *
        ((Set.ncard {k : ℤ | k ^ 2 = ((n - i : ℕ) : ℤ)} : ℕ) : ℤ) ∧
    (n : ℤ) * ((Set.ncard {k : ℕ | k * (k + 1) / 2 = n} : ℕ) : ℤ) =
      ∑ i ∈ Finset.Icc 1 n, (dF i) * ((Set.ncard {k : ℕ | k * (k + 1) / 2 = n - i} : ℕ) : ℤ) ∧
    (n : ℤ) * pd n = ∑ i ∈ Finset.Icc 1 n, (dG i) * pd (n - i)

/-- **Recurrences for partitions into even or distinct parts and for overpartitions.** Let $n$
be a natural number. Let $p_e(m)$, $p_o(m)$ and $p_d(m)$ be the numbers of partitions of $m$
into even parts, into odd parts and into distinct parts, and let $\bar p(m)$ be the number of
overpartitions of $m$. For a positive integer $m$, write $\sigma(m)$ for the sum of the divisors
of $m$, $\sigma(m/2)$ for $\sigma$ evaluated at $m/2$ when $m$ is even and for $0$ when $m$ is
odd, $d_B(m)$ and $d_C(m)$ for the sums of the odd and of the even divisors of $m$, $d_D(m)$ for
the sum of the divisors $d$ of $m$ with $m/d$ odd, and $d_G(m) = \sum_{d \mid m} (-1)^{m/d-1} d$.
Then, with every sum running over $1 \le i \le n$,
$n\,p_e(n) = \sum_i d_C(i)\,p_e(n-i) = 2\sum_i \sigma(i/2)\,p_e(n-i)$,
$n\,p_d(n) = \sum_i d_B(i)\,p_o(n-i) = \sum_i d_G(i)\,p_d(n-i) =
\sum_i (\sigma(i) - 2\sigma(i/2))\,p_d(n-i)$, and
$n\,\bar p(n) = 2\sum_i d_D(i)\,\bar p(n-i) = 2\sum_i (\sigma(i) - \sigma(i/2))\,\bar p(n-i)$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 10
(`jis-2024-24.1.6-thm-10`). -/
public theorem_wanted glaisher_partition_recurrences (n : ℕ) :
    ((n : ℤ) * pe n = ∑ i ∈ Finset.Icc 1 n, (dC i) * pe (n - i) ∧
      ∑ i ∈ Finset.Icc 1 n, (dC i) * pe (n - i) =
        2 * ∑ i ∈ Finset.Icc 1 n, (σdiv 2 i) * pe (n - i)) ∧
    ((n : ℤ) * pd n = ∑ i ∈ Finset.Icc 1 n, (dB i) * po (n - i) ∧
      ∑ i ∈ Finset.Icc 1 n, (dB i) * po (n - i) = ∑ i ∈ Finset.Icc 1 n, (dG i) * pd (n - i) ∧
      ∑ i ∈ Finset.Icc 1 n, (dG i) * pd (n - i) =
        ∑ i ∈ Finset.Icc 1 n, ((σ₁ i) - 2 * σdiv 2 i) * pd (n - i)) ∧
    ((n : ℤ) * pbar n = 2 * ∑ i ∈ Finset.Icc 1 n, (dD i) * pbar (n - i) ∧
      2 * ∑ i ∈ Finset.Icc 1 n, (dD i) * pbar (n - i) =
        2 * ∑ i ∈ Finset.Icc 1 n, ((σ₁ i) - σdiv 2 i) * pbar (n - i))

/-- **Recurrences for sums of squares and sums of triangular numbers.** Let $m \ge 1$ be an
integer. For $n \ge 0$, let $r_m(n)$ be the number of $x \in \mathbb{Z}^m$ with
$x_1^2 + \dots + x_m^2 = n$, and let $t_m(n)$ be the number of $x \in \mathbb{Z}_{\ge 0}^m$ with
$\sum_{i=1}^{m} x_i(x_i+1)/2 = n$. Let $\sigma$ be the sum-of-divisors function, and set
$\sigma(j/2) = 0$ when $j$ is odd. Then for every $n \ge 0$,
$$n\,r_m(n) = m \sum_{j=1}^{n} 2(-1)^{j+1}\bigl(\sigma(j) - \sigma(j/2)\bigr)\,r_m(n-j)$$
and
$$n\,t_m(n) = m \sum_{j=1}^{n} \bigl(\sigma(j) - 4\sigma(j/2)\bigr)\,t_m(n-j).$$

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 11
(`jis-2024-24.1.6-thm-11`). -/
public theorem_wanted sum_squares_triangular_power_recurrences (m : ℕ) (hm : 0 < m)
    (n : ℕ) :
    (n : ℤ) * rsq m n = (m : ℤ) * ∑ j ∈ Finset.Icc 1 n,
      2 * (-1) ^ (j + 1) * ((σ₁ j) - σdiv 2 j) * rsq m (n - j) ∧
    (n : ℤ) * ttri m n = (m : ℤ) * ∑ j ∈ Finset.Icc 1 n,
      ((σ₁ j) - 4 * σdiv 2 j) * ttri m (n - j)

open Classical in
/-- **Six recursions for Glaisher's divisor functions from the theta functions.** Let $n \ge 1$
be a natural number. Write $\sigma(m)$ for the sum of the positive divisors of $m$, $d_D(m)$ for
the sum of the divisors $d$ of $m$ with $m/d$ odd, $d_F(m) = \sum_{d \mid m} (-1)^{d-1} d$,
$\bar\sigma_3(m) = \sum_{d \mid m,\ m/d \text{ odd}} d^3$,
$\tilde\sigma_3(m) = \sum_{d \mid m} (-1)^{d-1} d^3$ and $S(m) = \sigma(m) - 4\sigma(m/4)$, where
$\sigma(m/4) = 0$ unless $4 \mid m$; all of these are $0$ at every integer $m \le 0$. Then
$d_D(n) + 2\sum_{j=1}^{n} (-1)^j d_D(n-j^2)$ is $(-1)^{n-1} n$ if $n$ is a perfect square and
$0$ otherwise; $\sum_{j=0}^{n} d_F(n-j(j+1)/2)$ is $n$ if $n = k(k+1)/2$ for some natural number
$k$ and $0$ otherwise; $8\sum_{j=1}^{n-1} (-1)^{j+1} d_D(j)\,S(n-j) = n\,S(n) + (-1)^n d_D(n)$;
$4\sum_{j=1}^{n} d_F(j)\,\sigma(2n+1-2j) = n\,\sigma(2n+1)$;
$16\sum_{j=1}^{n-1} d_D(j)\,\tilde\sigma_3(n-j) = d_D(n) - n\,\tilde\sigma_3(n)$; and
$8\sum_{j=1}^{n} d_F(j)\,\bar\sigma_3(n+1-j) = n\,\bar\sigma_3(n+1)$.

These recursions come from the theta functions $\varphi(q) = \sum_{k \in \mathbb{Z}} q^{k^2}$ and
$\psi(q) = \sum_{k \ge 0} q^{k(k+1)/2}$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 14
(`jis-2024-24.1.6-thm-14`). -/
public theorem_wanted glaisher_theta_divisor_recursions (n : ℕ) (hn : 0 < n) :
    (dD n) + 2 * ∑ j ∈ Finset.Icc 1 n, (-1) ^ j * dD (n - j ^ 2) =
      (if IsSquare n then (-1) ^ (n - 1) * (n : ℤ) else 0) ∧
    ∑ j ∈ Finset.range (n + 1), dF (n - j * (j + 1) / 2) =
      (if ∃ j : ℕ, j * (j + 1) / 2 = n then (n : ℤ) else 0) ∧
    8 * ∑ j ∈ Finset.Ioo 0 n, (-1) ^ (j + 1) * (dD j) * ((σ₁ (n - j)) - 4 * σdiv 4 (n - j)) =
      (n : ℤ) * ((σ₁ n) - 4 * σdiv 4 n) + (-1) ^ n * dD n ∧
    4 * ∑ j ∈ Finset.Icc 1 n, (dF j) * σ₁ (2 * n + 1 - 2 * j) = (n : ℤ) * σ₁ (2 * n + 1) ∧
    16 * ∑ j ∈ Finset.Ioo 0 n, (dD j) * σtilde₃ (n - j) = (dD n) - (n : ℤ) * σtilde₃ n ∧
    8 * ∑ j ∈ Finset.Icc 1 n, (dF j) * σbar₃ (n + 1 - j) = (n : ℤ) * σbar₃ (n + 1)

/-- **Power recursion lemma for nonzero integer exponents.** Let $K$ be a field of characteristic
zero, let $A$ be an invertible formal power series in $K[[X]]$, and let $u$ and $v$ be nonzero
integers. Write $a_u(k)$ and $a_v(k)$ for the coefficients of $X^k$ in $A^u$ and $A^v$. Then for
every natural number $n$,

$$\sum_{k=0}^{n} \left(n - \left(\frac{u}{v} + 1\right) k\right) a_u(n-k)\, a_v(k) = 0.$$

Invertibility of $A$ is assumed so that the negative powers $A^u$, $A^v$ make sense.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 17
(`jis-2024-24.1.6-lem-17`). -/
public theorem_wanted power_coeff_convolution_zpow {K : Type*} [Field K] [CharZero K]
    (A : (PowerSeries K)ˣ) (u v : ℤ) (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((n : K) - ((u : K) / v + 1) * k) * coeff (n - k) ((A ^ u : (PowerSeries K)ˣ) : PowerSeries K) *
        coeff k ((A ^ v : (PowerSeries K)ˣ) : PowerSeries K) = 0

/-- **Power recursion lemma for positive exponents.** Let $K$ be a field of characteristic zero,
let $A \in K[[X]]$ be a formal power series, and let $u$ and $v$ be positive integers. Write
$a_u(k)$ and $a_v(k)$ for the coefficients of $X^k$ in $A^u$ and $A^v$. Then for every natural
number $n$,

$$\sum_{k=0}^{n} \left(n - \left(\frac{u}{v} + 1\right) k\right) a_u(n-k)\, a_v(k) = 0.$$

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 17
(`jis-2024-24.1.6-lem-17`). -/
public theorem_wanted power_coeff_convolution_pow {K : Type*} [Field K] [CharZero K]
    (A : PowerSeries K) (u v : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((n : K) - ((u : K) / v + 1) * k) * coeff (n - k) (A ^ u) * coeff k (A ^ v) = 0

/-- **Six divisor-function identities from the power recursion lemma.** Let $n \ge 1$ be a
natural number. Write $\sigma(m)$ for the sum of the positive divisors of $m$,
$\bar\sigma_3(m) = \sum_{d \mid m,\ m/d \text{ odd}} d^3$,
$\tilde\sigma_3(m) = \sum_{d \mid m} (-1)^{d-1} d^3$ and $S(m) = \sigma(m) - 4\sigma(m/4)$, where
$\sigma(m/4) = 0$ unless $4 \mid m$; all of these are $0$ at every integer $m \le 0$. Then
$2n\,\sigma(2n+1) = \sum_{j=1}^{n} (5j(j+1) - 2n)\,\sigma(2n+1-j(j+1))$; the number
$n\,S(n) - 2\sum_{j=1}^{n} (5j^2 - n)\,S(n-j^2)$ is $n$ if $n$ is a perfect square and $0$
otherwise;
$n\,\bar\sigma_3(n+1) = \sum_{j=1}^{n+1} (9j(j+1)/2 - n)\,\bar\sigma_3(n+1-j(j+1)/2)$; the
number $n\,\tilde\sigma_3(n) - 2\sum_{j=1}^{n} (-1)^j (9j^2 - n)\,\tilde\sigma_3(n-j^2)$ is
$(-1)^{n-1} n$ if $n$ is a perfect square and $0$ otherwise;
$\sum_{j=0}^{n+1} (3j - n)\,\sigma(2j+1)\,\bar\sigma_3(n+1-j) = 0$; and
$n\,(\tilde\sigma_3(n) + (-1)^n S(n)) =
8\sum_{j=1}^{n-1} (3j - n)(-1)^j S(j)\,\tilde\sigma_3(n-j)$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 19
(`jis-2024-24.1.6-thm-19`). -/
public theorem_wanted glaisher_power_recursion_divisor_identities (n : ℕ) (hn : 0 < n) :
    2 * (n : ℤ) * σ₁ (2 * n + 1) = ∑ j ∈ Finset.Icc 1 n,
      (5 * (j : ℤ) * (j + 1) - 2 * n) * σ₁ (2 * n + 1 - j * (j + 1)) ∧
    (n : ℤ) * ((σ₁ n) - 4 * σdiv 4 n) - 2 * ∑ j ∈ Finset.Icc 1 n,
      (5 * (j : ℤ) ^ 2 - n) * ((σ₁ (n - j ^ 2)) - 4 * σdiv 4 (n - j ^ 2)) =
      (if IsSquare n then (n : ℤ) else 0) ∧
    (n : ℤ) * σbar₃ (n + 1) = ∑ j ∈ Finset.Icc 1 (n + 1),
      (9 * (((j * (j + 1) / 2 : ℕ)) : ℤ) - n) * σbar₃ (n + 1 - j * (j + 1) / 2) ∧
    (n : ℤ) * (σtilde₃ n) - 2 * ∑ j ∈ Finset.Icc 1 n,
      (-1) ^ j * (9 * (j : ℤ) ^ 2 - n) * σtilde₃ (n - j ^ 2) =
      (if IsSquare n then (-1) ^ (n - 1) * (n : ℤ) else 0) ∧
    ∑ j ∈ Finset.range (n + 2), (3 * (j : ℤ) - n) * (σ₁ (2 * j + 1)) * σbar₃ (n + 1 - j) = 0 ∧
    (n : ℤ) * ((σtilde₃ n) + (-1) ^ n * ((σ₁ n) - 4 * σdiv 4 n)) =
      8 * ∑ j ∈ Finset.Ioo 0 n,
        (3 * (j : ℤ) - n) * (-1) ^ j * ((σ₁ j) - 4 * σdiv 4 j) * σtilde₃ (n - j)

open Classical in
/-- **Glaisher's congruences for divisor sums over squares and triangular numbers.** Let
$n \ge 1$ be a natural number. Write $\sigma(m)$ for the sum of the positive divisors of $m$
and $\bar\sigma_3(m) = \sum_{d \mid m,\ m/d \text{ odd}} d^3$, and set
$\sigma(m) = \bar\sigma_3(m) = 0$ for every integer $m \le 0$. Then the following hold. If
$5 \nmid n$, then $\sum_{j=0}^{n} \sigma(2n+1-j(j+1)) \equiv 0 \pmod 5$. The sum
$\sum_{j=0}^{n} \sigma(n-j(j+1)/2)$ is congruent modulo $4$ to $n$ if $n = k(k+1)/2$ for some
natural number $k$, and to $0$ otherwise. If $5 \nmid n$ and $n \equiv 2$ or $3 \pmod 4$, then
$\sigma(n) + 2\sum_{j=1}^{n} \sigma(n-j^2) \equiv 0 \pmod 5$. If $n$ is coprime to $3$, then
$\sum_{j=0}^{n+1} \bar\sigma_3(n+1-j(j+1)/2) \equiv 0 \pmod 9$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 20
(`jis-2024-24.1.6-thm-20`). -/
public theorem_wanted glaisher_divisor_sum_congruences (n : ℕ) (hn : 0 < n) :
    (¬ 5 ∣ n → ∑ j ∈ Finset.range (n + 1), σ₁ (2 * n + 1 - j * (j + 1)) ≡ 0 [ZMOD 5]) ∧
    ∑ j ∈ Finset.range (n + 1), σ₁ (n - j * (j + 1) / 2) ≡
      (if ∃ k : ℕ, k * (k + 1) / 2 = n then (n : ℤ) else 0) [ZMOD 4] ∧
    (¬ 5 ∣ n → (n % 4 = 3 ∨ n % 4 = 2) →
      (σ₁ n) + 2 * ∑ j ∈ Finset.Icc 1 n, σ₁ (n - j ^ 2) ≡ 0 [ZMOD 5]) ∧
    (Nat.Coprime n 3 →
      ∑ j ∈ Finset.range (n + 2), σbar₃ (n + 1 - j * (j + 1) / 2) ≡ 0 [ZMOD 9])

open Classical in
/-- **A congruence modulo 5 for divisor sums over triangular shifts.** Let $\sigma$ be the
sum-of-divisors function, with $\sigma(r) = 0$ for $r \le 0$. For every integer $n \ge 1$, the sum
$\sum_{j=0}^{n} \sigma\bigl(2n + 1 - j(j+1)\bigr)$ is congruent to $1$ modulo $5$ if
$n = 5k(k+1)/2$ for some integer $k \ge 0$, and to $0$ modulo $5$ otherwise.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 23
(`jis-2024-24.1.6-thm-23`). -/
public theorem_wanted sigma_triangular_shift_sum_mod_five (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ Finset.range (n + 1), σ₁ (2 * n + 1 - j * (j + 1)) ≡
      (if ∃ k : ℕ, 5 * k * (k + 1) / 2 = n then 1 else 0) [ZMOD 5]

/-- **Convolution identities for the series-divisor of an invertible series.** Let $R$ be a
commutative ring and let $A$, $B$ be formal power series over $R$ with coefficients $a(k)$,
$b(k)$ and $AB = 1$. Let $s : \mathbb{N} \to R$ satisfy $s(0) = 0$ and
$k\,a(k) = \sum_{i=1}^{k} s(i)\,a(k-i)$ for every $k \ge 0$ (that is, $s$ is a series-divisor
of $A$). Then for every $n \ge 0$,
$$s(n) = \sum_{i=0}^{n} (n-i)\,a(n-i)\,b(i)$$
and
$$\sum_{i=1}^{n} s(n-i)\,s(i) = -\sum_{i=1}^{n} i\,(n-i)\,a(n-i)\,b(i).$$

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 25
(`jis-2024-24.1.6-lem-25`). -/
public theorem_wanted series_divisor_inverse_convolution {R : Type*} [CommRing R]
    (A B : PowerSeries R) (hAB : A * B = 1) (s : ℕ → R) (hs0 : s 0 = 0)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) A)
    (n : ℕ) :
    s n = ∑ i ∈ Finset.range (n + 1), ((n - i : ℕ) : R) * coeff (n - i) A * coeff i B ∧
    ∑ i ∈ Finset.Icc 1 n, s (n - i) * s i =
      -∑ i ∈ Finset.Icc 1 n, ((i * (n - i) : ℕ) : R) * coeff (n - i) A * coeff i B

/-- **Overpartition formulas for a divisor sum with odd cofactors.** Let $n$ be a natural number.
Write $\sigma(m)$ for the sum of the positive divisors of $m$, $\sigma(m/2)$ for $\sigma$
evaluated at $m/2$ when $m$ is even and for $0$ when $m$ is odd, and $d_D(m)$ for the sum of the
divisors $d$ of $m$ with $m/d$ odd, with $\sigma(0) = d_D(0) = 0$; let $\bar p(m)$ be the number
of overpartitions of $m$. Then $2 d_D(n) = 2(\sigma(n) - \sigma(n/2)) = n\,\bar p(n) +
2\sum_{i \ge 1,\ i^2 \le n} (-1)^i (n - i^2)\,\bar p(n - i^2)$ and
$2\sum_{i=1}^{n} d_D(n-i)\,d_D(i) =
\sum_{i \ge 1,\ i^2 \le n} (-1)^{i+1} i^2 (n - i^2)\,\bar p(n - i^2)$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 26
(`jis-2024-24.1.6-thm-26`). -/
public theorem_wanted overpartition_glaisher_dD_formulas (n : ℕ) :
    (2 * (dD n) = 2 * ((σ₁ n) - σdiv 2 n) ∧
      2 * ((σ₁ n) - σdiv 2 n) = (n : ℤ) * pbar n +
        2 * ∑ i ∈ Finset.Icc 1 n with i ^ 2 ≤ n,
          (-1) ^ i * ((n : ℤ) - (i : ℤ) ^ 2) * pbar (n - i ^ 2)) ∧
    2 * ∑ i ∈ Finset.Icc 1 n, (dD (n - i)) * dD i =
      ∑ i ∈ Finset.Icc 1 n with i ^ 2 ≤ n,
        (-1) ^ (i + 1) * (i : ℤ) ^ 2 * ((n : ℤ) - (i : ℤ) ^ 2) * pbar (n - i ^ 2)

/-- **Ramanujan's congruence modulo $5$ and a convolution of divisor sums.** Let $p(k)$ be the
number of partitions of $k$ and $\sigma(k)$ the sum of the positive divisors of $k$. Then
$p(5m+4) \equiv 0 \pmod 5$ for every natural number $m$ if and only if
$\sum_{i=1}^{5m} \sigma(i)\,\sigma(5m+1-i) \equiv 0 \pmod 5$ for every natural number $m$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 28
(`jis-2024-24.1.6-thm-28`). -/
public theorem_wanted partition_mod_five_iff_sigma_convolution :
    (∀ m : ℕ, Fintype.card (Nat.Partition (5 * m + 4)) ≡ 0 [MOD 5]) ↔
      ∀ m : ℕ, ∑ i ∈ Finset.Icc 1 (5 * m), σ 1 i * σ 1 (5 * m + 1 - i) ≡ 0 [MOD 5]

/-- **Overpartitions modulo $8$ and a convolution of divisor sums.** Let $\bar p(k)$ be the
number of overpartitions of $k$, and let $d_D(k)$ be the sum of the divisors $d$ of $k$ for which
$k/d$ is odd. Then $\bar p(4m+3) \equiv 0 \pmod 8$ for every natural number $m$ if and only if
$\sum_{i=1}^{4m-1} d_D(i)\,d_D(4m-i) \equiv 0 \pmod 4$ for every natural number $m$.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 30
(`jis-2024-24.1.6-thm-30`). -/
public theorem_wanted overpartition_mod_eight_iff_dD_convolution :
    (∀ m : ℕ, Nat.card (Nat.Overpartition (4 * m + 3)) ≡ 0 [MOD 8]) ↔
      ∀ m : ℕ, ∑ i ∈ Finset.Ioo 0 (4 * m), (dD i) * dD (4 * m - i) ≡ 0 [ZMOD 4]

end

end MetaMathlibExt
