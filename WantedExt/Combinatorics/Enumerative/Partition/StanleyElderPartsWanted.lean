/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import MathlibExt.Combinatorics.Enumerative.Partition.StanleyElderParts

/-!
# Stanley's and Elder's theorems on parts of partitions

The two classical results quoted in the introduction of Shruti Sharma and Amandeep Kaur,
*Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, and the paper's
`n`-color divisor-sum corollaries whose objects the records define (the rest are listed as
blocked in the audit table).

The paper's generating-function theorems (Theorems 3-12, stated "for `|q| < 1`") are stated as
identities of formal power series in `ℚ⟦X⟧`, with `q = X`, infinite sums and products taken in
the coefficientwise (`PowerSeries.WithPiTopology`) topology and `(1 ∓ q^k)⁻¹` the power-series
inverse.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Elder's theorem.** Let $n$ and $k$ be natural numbers with $k \ge 1$. The total number of
times the part $k$ occurs, counted with multiplicity, over all partitions of $n$ equals the sum,
over all partitions $\lambda$ of $n$, of the number of distinct parts of $\lambda$ that occur at
least $k$ times in $\lambda$.

The hypothesis $k \ge 1$ is needed: for $k = 0$ and $n = 1$ the left side is $0$ and the right
side is $1$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 2 (Elder's theorem). -/
public theorem_wanted sum_count_eq_sum_card_parts_count_ge (n k : ℕ) (hk : 1 ≤ k) :
    ∑ p : Nat.Partition n, p.parts.count k =
      ∑ p : Nat.Partition n, (p.parts.toFinset.filter fun i => k ≤ p.parts.count i).card

/-- **Total number of parts of $n$-color partitions via the divisor sum.** For $r \ge 0$ let
$C(r)$ be the number of $n$-color partitions of $r$, and let $T_o(r)$ (resp. $T_e(r)$) be the
total number of parts, counted with multiplicity, over the $n$-color partitions of $r$ having an
odd (resp. even) number of parts. Then for every $m \ge 1$,
$$T_o(m) + T_e(m) = \sum_{k=1}^{m} \sigma(k)\, C(m-k),$$
where $\sigma(k)$ is the sum of the divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 1 (`integers-2025-A94-cor-1`). -/
public theorem_wanted nColor_totalParts_eq_sum_sigma (m : ℕ) (hm : 1 ≤ m) :
    (∑ s ∈ (nColorPartitions m).filter (fun s => Odd s.card), s.card) +
        ∑ s ∈ (nColorPartitions m).filter (fun s => Even s.card), s.card =
      ∑ k ∈ Finset.Icc 1 m, ArithmeticFunction.sigma 1 k * (nColorPartitions (m - k)).card

/-- **Odd-divisor sum via the total number of parts of $n$-color partitions.** For $r \ge 0$
let $T_o(r)$ (resp. $T_e(r)$) be the total number of parts, counted with multiplicity, over the
$n$-color partitions of $r$ having an odd (resp. even) number of parts, and let $C(D, r)$ be the
number of $n$-color partitions of $r$ into distinct colored parts. Then for every $m \ge 1$,
$$\sigma_{\mathrm{odd}}(m) = \sum_{k=1}^{m} \bigl(T_o(k) - T_e(k)\bigr)\, C(D, m-k),$$
where $\sigma_{\mathrm{odd}}(m)$ is the sum of the odd divisors of $m$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 2 (`integers-2025-A94-cor-2`). -/
public theorem_wanted sigmaOdd_eq_sum_nColor_partsDiff_mul_distinct (m : ℕ) (hm : 1 ≤ m) :
    (sigmaOdd m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => Odd s.card), s.card : ℕ) : ℤ) -
            ((∑ s ∈ (nColorPartitions k).filter (fun s => Even s.card), s.card : ℕ) : ℤ)) *
          ((nColorPartitions (m - k)).filter fun s => s.Nodup).card

/-- **Even divisor sums count the even parts of $n$-color partitions.** For $m \ge 1$, let
$A_e(m)$ be the total number of parts of even size, counted with multiplicity, over the
$n$-color partitions of $m$, and for $r \ge 0$ let $C(r)$ be the number of $n$-color partitions
of $r$. Then
$$A_e(m) = \sum_{k=1}^{m} \sigma_{\mathrm{even}}(k) \, C(m - k),$$
where $\sigma_{\mathrm{even}}(k)$ is the sum of the even divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 3 (`integers-2025-A94-cor-3`). -/
public theorem_wanted nColor_evenParts_eq_sum_sigmaEven (m : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ nColorPartitions m, (s.filter fun p => Even p.1).card =
      ∑ k ∈ Finset.Icc 1 m, sigmaEven k * (nColorPartitions (m - k)).card

/-- **Number of odd parts in n-color partitions as a divisor sum.** For $i \ge 0$ let $A_o(i)$ be
the total number of odd parts (parts of odd size, counted with multiplicity) over the $n$-color
partitions of $i$, and let $C(i)$ be the number of $n$-color partitions of $i$. Then for every
$m \ge 1$,
$$
A_o(m) = \sum_{k=1}^{m} \sigma_{\mathrm{odd}}(k)\, C(m-k),
$$
where $\sigma_{\mathrm{odd}}(k)$ is the sum of the odd divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 4 (`integers-2025-A94-cor-4`). -/
public theorem_wanted nColor_oddParts_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ nColorPartitions m, (s.filter fun p => Odd p.1).card =
      ∑ k ∈ Finset.Icc 1 m, sigmaOdd k * (nColorPartitions (m - k)).card

/-- **Parts in a residue class over n-color partitions as a divisor sum.** Let $r$ and $k$ be
natural numbers with $0 < k < r$. For $i \ge 0$ let $C(k \bmod r, i)$ be the total number of
parts of size congruent to $k$ modulo $r$, counted with multiplicity, over the $n$-color
partitions of $i$, and let $C(i)$ be the number of $n$-color partitions of $i$. Then for every
$m \ge 1$,
$$
C(k \bmod r, m) = \sum_{j=1}^{m} \Bigl(\sum_{d \mid j,\ d \equiv k \pmod{r}} d\Bigr) C(m-j).
$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 6 (`integers-2025-A94-cor-6`). -/
public theorem_wanted nColor_partsModEq_eq_sum (m r k : ℕ) (hm : 1 ≤ m) (hk : 0 < k)
    (hkr : k < r) :
    ∑ s ∈ nColorPartitions m, (s.filter fun p => p.1 % r = k).card =
      ∑ j ∈ Finset.Icc 1 m,
        (∑ d ∈ j.divisors.filter (fun d => d % r = k), d) * (nColorPartitions (m - j)).card

/-- **Odd divisor sums count the parts of distinct $n$-color partitions.** Call an $n$-color
partition distinct when no colored part occurs more than once. For $m \ge 1$, let $C_o(D, m)$
(resp. $C_e(D, m)$) be the total number of parts over the distinct $n$-color partitions of $m$
with an odd (resp. even) number of parts, and for $r \ge 0$ let $C(D, r)$ be the number of
distinct $n$-color partitions of $r$. Then
$$C_o(D, m) + C_e(D, m) = \sum_{k=1}^{m} \sigma_{\mathrm{odd}}(k) \, C(D, m - k),$$
where $\sigma_{\mathrm{odd}}(k)$ is the sum of the odd divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 7 (`integers-2025-A94-cor-7`). -/
public theorem_wanted nColor_distinctTotalParts_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    (∑ s ∈ (nColorPartitions m).filter (fun s => s.Nodup ∧ Odd s.card), s.card) +
        ∑ s ∈ (nColorPartitions m).filter (fun s => s.Nodup ∧ Even s.card), s.card =
      ∑ k ∈ Finset.Icc 1 m, sigmaOdd k * ((nColorPartitions (m - k)).filter fun s => s.Nodup).card

/-- **Divisor sum via distinct $n$-color partitions.** For $r \ge 0$ let $C(r)$ be the number
of $n$-color partitions of $r$, and let $C_o(D, r)$ (resp. $C_e(D, r)$) be the total number of
parts over the $n$-color partitions of $r$ into an odd (resp. even) number of distinct colored
parts. Then for every $m \ge 1$,
$$\sigma(m) = \sum_{k=1}^{m} \bigl(C_o(D, k) - C_e(D, k)\bigr)\, C(m-k),$$
where $\sigma(m)$ is the sum of the divisors of $m$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 8 (`integers-2025-A94-cor-8`). -/
public theorem_wanted sigma_eq_sum_nColor_distinctPartsDiff (m : ℕ) (hm : 1 ≤ m) :
    (ArithmeticFunction.sigma 1 m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Odd s.card), s.card : ℕ) : ℤ) -
            ((∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) :
              ℤ)) *
          (nColorPartitions (m - k)).card

/-- **Number of parts in n-color partitions into odd parts as a divisor sum.** For $i \ge 0$ let
$Q(O, i)$ be the total number of parts, counted with multiplicity, over the $n$-color partitions
of $i$ into odd parts (every part has odd size), and let $C(O, i)$ be the number of such
partitions. Then for every $m \ge 1$,
$$
Q(O, m) = \sum_{k=1}^{m} \sigma_{\mathrm{odd}}(k)\, C(O, m-k),
$$
where $\sigma_{\mathrm{odd}}(k)$ is the sum of the odd divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 10 (`integers-2025-A94-cor-10`). -/
public theorem_wanted nColor_oddPartitionParts_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ (nColorPartitions m).filter (fun s => ∀ p ∈ s, Odd p.1), s.card =
      ∑ k ∈ Finset.Icc 1 m,
        sigmaOdd k * ((nColorPartitions (m - k)).filter fun s => ∀ p ∈ s, Odd p.1).card

/-- **Odd divisor sums count the parts of $n$-color partitions into odd parts.** Say that an
$n$-color partition has odd parts when every part has odd size. For $m \ge 1$, let $U_o(m)$
(resp. $U_e(m)$) be the total number of parts over the $n$-color partitions of $m$ with odd parts
and an odd (resp. even) number of parts, and for $r \ge 0$ let $C(O, r)$ be the number of
$n$-color partitions of $r$ with odd parts. Then
$$U_o(m) + U_e(m) = \sum_{k=1}^{m} \sigma_{\mathrm{odd}}(k) \, C(O, m - k),$$
where $\sigma_{\mathrm{odd}}(k)$ is the sum of the odd divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 12 (`integers-2025-A94-cor-12`). -/
public theorem_wanted nColor_oddPartitionParts_byParity_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    (∑ s ∈ (nColorPartitions m).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card), s.card) +
        ∑ s ∈ (nColorPartitions m).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card =
      ∑ k ∈ Finset.Icc 1 m,
        sigmaOdd k * ((nColorPartitions (m - k)).filter fun s => ∀ p ∈ s, Odd p.1).card


/-- **Generating functions for the total number of parts of $n$-color partitions.** For
$m \ge 0$ let $T_o(m)$ (resp. $T_e(m)$) be the total number of parts, counted with
multiplicity, over the $n$-color partitions of $m$ having an odd (resp. even) number of parts.
Then, as formal power series in $q$ with rational coefficients,
$$\sum_{m \ge 1} \frac{m q^m}{1 - q^m} =
\prod_{m \ge 1} (1 - q^m)^m \sum_{m \ge 0} \bigl(T_o(m) + T_e(m)\bigr) q^m$$
and
$$\sum_{m \ge 1} \frac{m q^m}{1 + q^m} =
\prod_{m \ge 1} (1 + q^m)^m \sum_{m \ge 0} \bigl(T_o(m) - T_e(m)\bigr) q^m.$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 3 (`integers-2025-A94-thm-3`). -/
public theorem_wanted nColor_totalParts_generatingFunction :
    (∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 - X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => Odd s.card), s.card : ℕ) : ℚ) +
              ((∑ s ∈ (nColorPartitions n).filter (fun s => Even s.card), s.card : ℕ) : ℚ)) ∧
      ∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 + X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 + X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => Odd s.card), s.card : ℕ) : ℚ) -
              ((∑ s ∈ (nColorPartitions n).filter (fun s => Even s.card), s.card : ℕ) : ℚ)

/-- **Generating function for the number of odd parts in n-color partitions.** For $i \ge 0$ let
$A_o(i)$ be the total number of odd parts (parts of odd size, counted with multiplicity) over the
$n$-color partitions of $i$. Then in the ring $\mathbb{Q}[[q]]$ of formal power series, with
infinite sums and products taken coefficientwise,
$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 - q^{2m+1}} =
\prod_{m \ge 1} (1 - q^m)^m \sum_{i \ge 0} A_o(i)\, q^i.
$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 5 (`integers-2025-A94-thm-5`). -/
public theorem_wanted nColor_oddParts_generatingFunction :
    ∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 - X ^ (2 * m + 1))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ nColorPartitions n, (s.filter fun p => Odd p.1).card : ℕ) : ℚ)

/-- **Generating function for parts in a residue class over n-color partitions.** Let $r$ and
$k$ be natural numbers with $0 < k < r$, and for $i \ge 0$ let $C(k \bmod r, i)$ be the total
number of parts of size congruent to $k$ modulo $r$, counted with multiplicity, over the
$n$-color partitions of $i$. Then in the ring $\mathbb{Q}[[q]]$ of formal power series, with
infinite sums and products taken coefficientwise,
$$
\sum_{m \ge 0} \frac{(rm+k)\,q^{rm+k}}{1 - q^{rm+k}} =
\prod_{m \ge 1} (1 - q^m)^m \sum_{i \ge 0} C(k \bmod r, i)\, q^i.
$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 7 (`integers-2025-A94-thm-7`). -/
public theorem_wanted nColor_partsModEq_generatingFunction (r k : ℕ) (hk : 0 < k) (hkr : k < r) :
    ∑' m : ℕ, ((r * m + k : ℕ) : ℚ⟦X⟧) * X ^ (r * m + k) * (1 - X ^ (r * m + k))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ nColorPartitions n, (s.filter fun p => p.1 % r = k).card : ℕ) : ℚ)

/-- **Generating functions for the parts of distinct $n$-color partitions.** Call an $n$-color
partition distinct when no colored part occurs more than once, and let $C_o(D, m)$ (resp.
$C_e(D, m)$) be the total number of parts over the distinct $n$-color partitions of $m$ with an
odd (resp. even) number of parts. Then, as formal power series in $q$ over $\mathbb{Q}$, with
infinite sums and products taken coefficientwise, both
$$
\sum_{m \ge 1} \frac{m q^m}{1 + q^m} =
\Big(\prod_{m \ge 1} (1 + q^m)^m\Big)^{-1} \sum_{m \ge 0} \big(C_o(D, m) + C_e(D, m)\big) q^m
$$
and
$$
\sum_{m \ge 1} \frac{m q^m}{1 - q^m} =
\Big(\prod_{m \ge 1} (1 - q^m)^m\Big)^{-1} \sum_{m \ge 0} \big(C_o(D, m) - C_e(D, m)\big) q^m
$$
hold.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 8 (`integers-2025-A94-thm-8`). -/
public theorem_wanted nColor_distinctTotalParts_generatingFunction :
    (∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 + X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 + X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧)⁻¹ *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Odd s.card), s.card : ℕ) : ℚ) +
              ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Even s.card),
                s.card : ℕ) : ℚ)) ∧
      ∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 - X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧)⁻¹ *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Odd s.card), s.card : ℕ) : ℚ) -
              ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) : ℚ)

/-- **Odd-divisor sum via distinct $n$-color partitions and signed partition counts.** For
$r \ge 0$ let $C_o(D, r)$ (resp. $C_e(D, r)$) be the total number of parts over the $n$-color
partitions of $r$ into an odd (resp. even) number of distinct colored parts, and let
$C_{e-o}(r) = \sum_\lambda (-1)^{\ell(\lambda)}$, the sum running over all $n$-color partitions
$\lambda$ of $r$, where $\ell(\lambda)$ is the number of parts of $\lambda$ counted with
multiplicity. Then for every $m \ge 1$,
$$\sigma_{\mathrm{odd}}(m) =
\sum_{k=1}^{m} \bigl(C_o(D, k) + C_e(D, k)\bigr)\, C_{e-o}(m-k),$$
where $\sigma_{\mathrm{odd}}(m)$ is the sum of the odd divisors of $m$.

This is the reading given by the paper's derivation from Theorem 8 and Eq. (3). As printed,
with the number $C(D, k)$ of $n$-color partitions of $k$ into distinct colored parts in place
of $C_o(D, k) + C_e(D, k)$, it fails at $m = 3$: $\sigma_{\mathrm{odd}}(3) = 4$, but
$\sum_{k=1}^{3} C(D, k)\, C_{e-o}(3-k) = 1 \cdot (-1) + 2 \cdot (-1) + 5 \cdot 1 = 2$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 9 (`integers-2025-A94-cor-9`). -/
public theorem_wanted sigmaOdd_eq_sum_nColor_distinctTotalParts_mul_signed (m : ℕ) (hm : 1 ≤ m) :
    (sigmaOdd m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Odd s.card), s.card) +
            ∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) : ℤ) *
          ∑ s ∈ nColorPartitions (m - k), (-1 : ℤ) ^ s.card

/-- **Generating function for the number of parts in n-color partitions into odd parts.** For
$i \ge 0$ let $Q(O, i)$ be the total number of parts, counted with multiplicity, over the
$n$-color partitions of $i$ into odd parts (every part has odd size). Then in the ring
$\mathbb{Q}[[q]]$ of formal power series, with infinite sums and products taken coefficientwise,
$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 - q^{2m+1}} =
\prod_{m \ge 0} (1 - q^{2m+1})^{2m+1} \sum_{i \ge 0} Q(O, i)\, q^i.
$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 9 (`integers-2025-A94-thm-9`). -/
public theorem_wanted nColor_oddPartitionParts_generatingFunction :
    ∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 - X ^ (2 * m + 1))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (2 * m + 1)) ^ (2 * m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ (nColorPartitions n).filter (fun s => ∀ p ∈ s, Odd p.1), s.card : ℕ) : ℚ)

/-- **Generating function for parts of a given size in distinct $n$-color partitions.** Call an
$n$-color partition distinct when no colored part occurs more than once. For a natural number
$j$, let $Q(D, j, m)$ be the total number of parts of size $j$ (of any color) over the distinct
$n$-color partitions of $m$, and let $C(D, m)$ be the number of distinct $n$-color partitions of
$m$. Then, as formal power series in $q$ over $\mathbb{Q}$,
$$\sum_{m \ge 0} Q(D, j, m) \, q^m = \frac{j q^j}{1 + q^j} \sum_{m \ge 0} C(D, m) \, q^m.$$

The paper assumes $j \ge 1$; for $j = 0$ both sides vanish.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 11 (`integers-2025-A94-thm-11`). -/
public theorem_wanted nColor_distinctPartsCountOf_generatingFunction (j : ℕ) :
    (PowerSeries.mk fun n =>
        ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup), (s.filter fun p => p.1 = j).card :
          ℕ) : ℚ)) =
      (j : ℚ⟦X⟧) * X ^ j * (1 + X ^ j)⁻¹ *
        PowerSeries.mk fun n => (((nColorPartitions n).filter fun s => s.Nodup).card : ℚ)

/-- **Parts of n-color partitions into odd parts, by parity of the number of parts.** For
$i \ge 0$ let $U_o(i)$ (resp. $U_e(i)$) be the total number of parts, counted with multiplicity,
over the $n$-color partitions of $i$ into odd parts (every part has odd size) that have an odd
(resp. even) number of parts. Then in the ring $\mathbb{Q}[[q]]$ of formal power series, with
infinite sums and products taken coefficientwise,
$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 - q^{2m+1}} =
\prod_{m \ge 0} (1 - q^{2m+1})^{2m+1} \sum_{i \ge 0} \bigl(U_o(i) + U_e(i)\bigr) q^i
$$
and
$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 + q^{2m+1}} =
\prod_{m \ge 0} (1 + q^{2m+1})^{2m+1} \sum_{i \ge 0} \bigl(U_o(i) - U_e(i)\bigr) q^i.
$$

The paper's printed definition swaps the subscripts ($U_e$ for an odd number of parts); with it
the second identity fails at $q^1$: the left side has coefficient $1$, the right side
$U_o(1) - U_e(1) = 0 - 1 = -1$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 12 (`integers-2025-A94-thm-12`). -/
public theorem_wanted nColor_oddPartitionParts_byParity_generatingFunction :
    (∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 - X ^ (2 * m + 1))⁻¹ =
        (∏' m : ℕ, (1 - X ^ (2 * m + 1)) ^ (2 * m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card :
              ℕ) : ℚ) +
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card),
              s.card : ℕ) : ℚ)) ∧
      ∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 + X ^ (2 * m + 1))⁻¹ =
        (∏' m : ℕ, (1 + X ^ (2 * m + 1)) ^ (2 * m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card :
              ℕ) : ℚ) -
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card),
              s.card : ℕ) : ℚ)

/-- **Signed odd-divisor sum via $n$-color partitions into odd parts.** For $r \ge 0$ let
$U_o(r)$ (resp. $U_e(r)$) be the total number of parts, counted with multiplicity, over the
$n$-color partitions of $r$ in which every part has odd size and the number of parts is odd
(resp. even), and let $C(O, D, r)$ be the number of $n$-color partitions of $r$ into distinct
colored parts all of odd size. Then for every $m \ge 1$,
$$(-1)^{m+1} \sigma_{\mathrm{odd}}(m) =
\sum_{k=1}^{m} \bigl(U_o(k) - U_e(k)\bigr)\, C(O, D, m-k),$$
where $\sigma_{\mathrm{odd}}(m)$ is the sum of the odd divisors of $m$.

The subscripts of $U_o$ and $U_e$ give the parity of the number of parts. With the printed
(swapped) definition of $U_o$ and $U_e$ the identity fails at $m = 1$: the left side is $1$
and the right side is $(0 - 1) \cdot 1 = -1$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 13 (`integers-2025-A94-cor-13`). -/
public theorem_wanted neg_one_pow_mul_sigmaOdd_eq_sum_nColor_oddPartsDiff (m : ℕ) (hm : 1 ≤ m) :
    (-1 : ℤ) ^ (m + 1) * sigmaOdd m =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card :
              ℕ) : ℤ) -
            ((∑ s ∈ (nColorPartitions k).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card),
              s.card : ℕ) : ℤ)) *
          ((nColorPartitions (m - k)).filter fun s => s.Nodup ∧ ∀ p ∈ s, Odd p.1).card

end

end MetaMathlibExt
