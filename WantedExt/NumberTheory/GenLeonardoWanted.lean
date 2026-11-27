/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import MathlibExt.NumberTheory.GenLeonardo
public import WantedExt.NumberTheory.LeonardoPWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Leonardo numbers as Leonardo $p$-numbers with $p = 1$.** For all natural numbers
$k$ and $n$, the generalized Leonardo number $L_{k,n}$ equals the generalized Leonardo $p$-number
$\mathcal{L}_{1,k}(n)$; both sequences start with $1, 1$ and satisfy the recurrence
$a_{n+2} = a_{n+1} + a_n + k$.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*,
Fibonacci Quarterly 62.3 (2024), introduction; Kusrini, Putra, and
Kuhapatanakul, *On Generalized Leonardo p-Numbers*, Journal of
Integer Sequences 27 (2024), Article 24.4.6. -/
public theorem_wanted genLeonardo_eq_leonardoPK_one (k n : ℕ) :
    genLeonardo (k : ℤ) n
      = MathlibExt.NumberTheory.LeonardoPWanted.leonardoPK 1 k n

/-- **Product of a generalized Leonardo number and its dual.** Let $k$ be an integer, and let
$L_{k,n}$ and $M_{k,n}$ denote the generalized Leonardo numbers and the dual generalized Leonardo
numbers. For every natural number $n$,
$$L_{k,n} M_{k,n} = (k+1) L_{k,2n+1} - k L_{k,n+3} + k\,(2k+1).$$

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.2 (`fq-2024-kuhapatanakul05292024-thm-2.2`). -/
public theorem_wanted genLeonardo_mul_companion (k : ℤ) (n : ℕ) :
    genLeonardo k n * genLeonardoCompanion k n
      = (k + 1) * genLeonardo k (2 * n + 1) - k * genLeonardo k (n + 3)
        + k * (2 * k + 1)

/-- **Cross-product identity for generalized Leonardo numbers.** Let $k$ be an integer, and let
$L_{k,n}$ and $M_{k,n}$ denote the generalized Leonardo numbers and the dual generalized Leonardo
numbers. For every natural number $n \ge 1$,
$$L_{k,n} M_{k,n+1} - L_{k,n+1} M_{k,n-1} = (k+1) L_{k,2n} - k L_{k,n} + k.$$

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.3 (`fq-2024-kuhapatanakul05292024-thm-2.3`). -/
public theorem_wanted genLeonardo_cross (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    genLeonardo k n * genLeonardoCompanion k (n + 1)
        - genLeonardo k (n + 1) * genLeonardoCompanion k (n - 1)
      = (k + 1) * genLeonardo k (2 * n) - k * genLeonardo k n + k

/-- **Binomial convolution identities for generalized Leonardo numbers.** Let $k$ be an integer,
and let $L_{k,n}$ and $M_{k,n}$ denote the generalized Leonardo numbers and the dual generalized
Leonardo numbers. For all natural numbers $n$ and $r$,
$$\sum_{i=0}^{n} \binom{n}{i} L_{k,i+r} = L_{k,2n+r} - k\,(2^n - 1)$$
and
$$\sum_{i=0}^{n} \binom{n}{i} M_{k,i+r} = M_{k,2n+r} - 2k\,(2^n - 1).$$

Parts (iii) and (iv) of the paper's Theorem 3.1, alternating sums involving the index
$L_{k,n-r-2}$, are false as printed: at $k = 1$, $n = 3$, $r = 1$, with the sequence extended to
negative indices by the recurrence, the left side is $2$ and the printed right side is $-2$.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 3.1 (i),(ii)
(`fq-2024-kuhapatanakul05292024-thm-3.1`). -/
public theorem_wanted genLeonardo_binomial_sum (k : ℤ) (n r : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardo k (i + r)
      = genLeonardo k (2 * n + r) - k * (2 ^ n - 1)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardoCompanion k (i + r)
      = genLeonardoCompanion k (2 * n + r) - 2 * k * (2 ^ n - 1))

/-- **Even-order binomial identities for generalized Leonardo numbers.** Let $k$ be an integer,
and let $L_{k,n}$ and $M_{k,n}$ denote the generalized Leonardo numbers and the dual generalized
Leonardo numbers. For all natural numbers $m$ and $r$,
$$\sum_{i=0}^{2m} \binom{2m}{i} L_{k,2i+r} = 5^m L_{k,2m+r} + k\,(5^m - 2^{2m})$$
and
$$\sum_{i=0}^{2m} \binom{2m}{i} M_{k,2i+r} = 5^m M_{k,2m+r} + 2k\,(5^m - 2^{2m}).$$

The paper's Theorem 3.2 also states identities of odd order $n$; as printed they are false (at
$k = n = 1$, $r = 0$ the first odd identity reads $4 = 6$).

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 3.2, even case
(`fq-2024-kuhapatanakul05292024-thm-3.2`). -/
public theorem_wanted genLeonardo_binomial_sum_two_mul (k : ℤ) (m r : ℕ) :
    (∑ i ∈ Finset.range (2 * m + 1),
        (Nat.choose (2 * m) i : ℤ) * genLeonardo k (2 * i + r)
      = 5 ^ m * genLeonardo k (2 * m + r) + k * (5 ^ m - 2 ^ (2 * m))) ∧
    (∑ i ∈ Finset.range (2 * m + 1),
        (Nat.choose (2 * m) i : ℤ) * genLeonardoCompanion k (2 * i + r)
      = 5 ^ m * genLeonardoCompanion k (2 * m + r) + 2 * k * (5 ^ m - 2 ^ (2 * m)))

/-- **Alternating binomial identities for generalized Leonardo numbers.** Let $k$ be an integer,
and let $L_{k,n}$ and $M_{k,n}$ denote the generalized Leonardo numbers and the dual generalized
Leonardo numbers. For all natural numbers $n \ge 1$ and $r$,
$$\sum_{i=0}^{n} \binom{n}{i} (-1)^{n-i} L_{k,2i+r} = L_{k,n+r} + k$$
and
$$\sum_{i=0}^{n} \binom{n}{i} (-1)^{n-i} M_{k,2i+r} = M_{k,n+r} + 2k.$$

The hypothesis $n \ge 1$ is needed: for $n = 0$ the two sums equal $L_{k,r}$ and $M_{k,r}$.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 3.3 (`fq-2024-kuhapatanakul05292024-thm-3.3`). -/
public theorem_wanted genLeonardo_binomial_alternating (k : ℤ) (n r : ℕ)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℤ) * (-1) ^ (n - i) * genLeonardo k (2 * i + r)
      = genLeonardo k (n + r) + k) ∧
    (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℤ) * (-1) ^ (n - i) * genLeonardoCompanion k (2 * i + r)
      = genLeonardoCompanion k (n + r) + 2 * k)

/-- **Binomial identities with steps three and four for generalized Leonardo numbers.** Let $k$ be
an integer, and let $L_{k,n}$ and $M_{k,n}$ denote the generalized Leonardo numbers and the dual
generalized Leonardo numbers. For all natural numbers $n$ and $r$,
$$\sum_{i=0}^{n} \binom{n}{i} L_{k,3i+r} = 2^n L_{k,2n+r},$$
$$\sum_{i=0}^{n} \binom{n}{i} M_{k,3i+r} = 2^n M_{k,2n+r},$$
$$\sum_{i=0}^{n} \binom{n}{i} L_{k,4i+r} = 3^n L_{k,2n+r} + k\,(3^n - 2^n),$$
and
$$\sum_{i=0}^{n} \binom{n}{i} M_{k,4i+r} = 3^n M_{k,2n+r} + 2k\,(3^n - 2^n).$$

Part (iv) of the paper's Theorem 3.4 prints the last term of the fourth identity as
$k\,(3^n - 2^n)$, which is false at $k = n = 1$, $r = 0$; the coefficient $2k$ is the correct one,
as in parts (ii) of Theorems 3.1–3.3.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 3.4 (`fq-2024-kuhapatanakul05292024-thm-3.4`). -/
public theorem_wanted genLeonardo_binomial_steps (k : ℤ) (n r : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardo k (3 * i + r)
      = 2 ^ n * genLeonardo k (2 * n + r)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardoCompanion k (3 * i + r)
      = 2 ^ n * genLeonardoCompanion k (2 * n + r)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardo k (4 * i + r)
      = 3 ^ n * genLeonardo k (2 * n + r) + k * (3 ^ n - 2 ^ n)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardoCompanion k (4 * i + r)
      = 3 ^ n * genLeonardoCompanion k (2 * n + r) + 2 * k * (3 ^ n - 2 ^ n))

end

end MetaMathlibExt
