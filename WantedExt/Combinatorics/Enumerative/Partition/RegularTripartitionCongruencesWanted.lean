/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan

/-!
# Congruences for `ℓ`-regular tripartitions, `ℓ ∈ {2, 3}` — wishlist

Statements from Mohammed L. Nadji and Moussa Ahmia, *Congruences for `l`-Regular
Tripartitions for `l` in `{2,3}`*, INTEGERS 24 (2024), Article A86.

`T_ℓ(n)` counts triples of `ℓ`-regular partitions (no part divisible by `ℓ`) of total
size `n`, i.e. `∑ T_ℓ(n) qⁿ = f_ℓ³ / f_1³` (paper, Section 1, eq. (1)), where
`f_k = (q^k; q^k)_∞` is `qEulerProduct k`, written `𝔣 k` below. Eta-quotient identities are
stated with denominators cleared (every `f_k` with `k ≥ 1` has constant coefficient `1`, so
it is a unit of `ℤ⟦X⟧`). The Cui–Gu `p`-dissections (Lemmas 4 and 5) involve Ramanujan's
`f(a, b)` with negated arguments and are stated for complex `q` with `‖q‖ < 1`, through
`ramanujanThetaRaw` and `qPochhammerInfRaw`.

Already stated elsewhere in this library: Lemma 2, eq. (4), is
`qPochhammer_three_dissection_product_one_two`; Lemma 3, eq. (5), is
`f1_cube_three_dissection`; Lemma 6, eq. (9), is the case `k = 1` of
`qEulerProduct_pow_prime_pow_congruence`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Regular tripartition counts.** For natural numbers $\ell$ and $n$, $T_\ell(n)$ is the number
of triples $(\lambda_1, \lambda_2, \lambda_3)$ of integer partitions with
$|\lambda_1| + |\lambda_2| + |\lambda_3| = n$ in which no part of any $\lambda_i$ is divisible by
$\ell$; these triples are the $\ell$-regular tripartitions of $n$.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Section 1, definition of `T_ℓ(n)` (with
generating function `f_ℓ³ / f_1³`, Section 1, eq. (1)). -/
public def regularTripartitionCount (l n : ℕ) : ℕ :=
  ∑ x ∈ Finset.antidiagonal n, ∑ y ∈ Finset.antidiagonal x.2,
    (Nat.Partition.restricted x.1 (¬ l ∣ ·)).card *
      (Nat.Partition.restricted y.1 (¬ l ∣ ·)).card *
      (Nat.Partition.restricted y.2 (¬ l ∣ ·)).card

private theorem card_restricted_zero (p : ℕ → Prop) [DecidablePred p] :
    (Nat.Partition.restricted 0 p).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨default, ?_⟩
  ext x
  simp [Nat.Partition.restricted, Subsingleton.elim x default]

private theorem card_restricted_one (p : ℕ → Prop) [DecidablePred p] (h : p 1) :
    (Nat.Partition.restricted 1 p).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨default, ?_⟩
  ext x
  simp [Nat.Partition.restricted, Subsingleton.elim x default, h]

/-- **The regular tripartition count at zero.** For every natural number $\ell$, $T_\ell(0) = 1$,
where $T_\ell(n)$ is the number of $\ell$-regular tripartitions of $n$: the only tripartition of
$0$ is the triple of empty partitions.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86 (definition of `T_ℓ(n)`). -/
public theorem regularTripartitionCount_zero (l : ℕ) : regularTripartitionCount l 0 = 1 := by
  simp [regularTripartitionCount, card_restricted_zero]

/-- **The number of $\ell$-regular tripartitions of $1$.** For every natural number $\ell \ne 1$,
the number $T_\ell(1)$ of $\ell$-regular tripartitions of $1$ is $3$: the single part $1$ lies in
one of the three components.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86 (definition of `T_ℓ(n)`). -/
public theorem regularTripartitionCount_one (l : ℕ) (hl : l ≠ 1) :
    regularTripartitionCount l 1 = 3 := by
  have h1 : ¬ l ∣ 1 := by simpa using hl
  simp [regularTripartitionCount, Finset.Nat.antidiagonal_succ, card_restricted_zero,
    card_restricted_one (fun x => ¬ l ∣ x) h1]

/-- **Congruences modulo 3 and 6 for 2-regular tripartitions.** Let $T_2(m)$ be the number of
$2$-regular tripartitions of $m$. For every natural number $n$, $3 \mid T_2(3n + 1)$ and
$6 \mid T_2(3n + 2)$.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Corollary 1. -/
public theorem_wanted regularTripartitionCount_two_mod_three_six (n : ℕ) :
    3 ∣ regularTripartitionCount 2 (3 * n + 1) ∧ 6 ∣ regularTripartitionCount 2 (3 * n + 2)

/-- **Congruences modulo 3 and 9 for 3-regular tripartitions.** Let $T_3(m)$ be the number of
$3$-regular tripartitions of $m$. For every natural number $n$, $3 \mid T_3(3n + 1)$ and
$9 \mid T_3(3n + 2)$.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Corollary 2 (congruences (53), (54)). -/
public theorem_wanted regularTripartitionCount_three_mod_three_nine (n : ℕ) :
    3 ∣ regularTripartitionCount 3 (3 * n + 1) ∧ 9 ∣ regularTripartitionCount 3 (3 * n + 2)

/-- **A congruence modulo 6 for 3-regular tripartitions.** Let $T_3(m)$ be the number of
$3$-regular tripartitions of $m$. For every natural number $n$, $6 \mid T_3(6n + 4)$.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Corollary 3 (congruence (64)). -/
public theorem_wanted regularTripartitionCount_three_six_mul_add_four (n : ℕ) :
    6 ∣ regularTripartitionCount 3 (6 * n + 4)

/-- **Even 2-regular tripartition counts for primes at least 5.** Let $T_2(n)$ be the number of
2-regular tripartitions of $n$. For every prime $p \ge 5$, all natural numbers $\alpha$ and $n$,
and every $i$ with $1 \le i \le p - 1$, the number
$T_2\bigl(3 p^{2\alpha+1} (p n + i) + (p^{2\alpha+2} - 1)/8\bigr)$ is even (the division is
exact).

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 1 (congruence (13)). -/
public theorem_wanted regularTripartitionCount_two_prime_ge_five_even
    (p α n i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hi : 1 ≤ i) (hip : i < p) :
    2 ∣ regularTripartitionCount 2
      (3 * p ^ (2 * α + 1) * (p * n + i) + (p ^ (2 * α + 2) - 1) / 8)

/-- **Even 2-regular tripartition counts for odd primes.** Let $T_2(n)$ be the number of 2-regular
tripartitions of $n$. For every odd prime $p$, all natural numbers $\alpha$ and $n$, and every $i$
with $1 \le i \le p - 1$, the number
$T_2\bigl(9 p^{2\alpha+1} (p n + i) + (9 p^{2\alpha+2} - 1)/8\bigr)$ is even (the division is
exact).

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 2 (congruence (21)). -/
public theorem_wanted regularTripartitionCount_two_odd_prime_even
    (p α n i : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hi : 1 ≤ i) (hip : i < p) :
    2 ∣ regularTripartitionCount 2
      (9 * p ^ (2 * α + 1) * (p * n + i) + (9 * p ^ (2 * α + 2) - 1) / 8)

/-- **A congruence modulo 3 for 3-regular tripartitions at primes $p \equiv 3 \pmod 4$.** Let
$T_3(m)$ be the number of $3$-regular tripartitions of $m$, and let $p$ be a prime with
$p \equiv 3 \pmod 4$. For all natural numbers $\alpha$ and $n$ and every integer $i$ with
$1 \le i \le p - 1$,
$$
T_3\Bigl(3 p^{2\alpha+1} (p n + i) + \frac{p^{2\alpha+2} - 1}{4}\Bigr) \equiv 0 \pmod 3,
$$
where the division by $4$ is exact.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 5 (congruence (55)). -/
public theorem_wanted regularTripartitionCount_three_prime_three_mod_four
    (p α n i : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (hi : 1 ≤ i) (hip : i < p) :
    3 ∣ regularTripartitionCount 3
      (3 * p ^ (2 * α + 1) * (p * n + i) + (p ^ (2 * α + 2) - 1) / 4)

local notation "𝔣" => qEulerProduct

/-- **Toh's 3-dissection of $f_2^3 / f_1^3$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler product, an integer power series in $q$. Then
$$
f_2^3 f_3^8 f_9 f_{18} = f_1^3 \bigl(f_3^7 f_6 f_9 f_{18} + 3q f_6^4 f_9^6 +
6q^2 f_3 f_6^3 f_9^3 f_{18}^3 + 12q^3 f_3^2 f_6^2 f_{18}^6\bigr).
$$

Since each $f_k$ has constant term $1$ and so is invertible, this is the identity
$f_2^3/f_1^3 = f_6/f_3 + 3q f_6^4 f_9^5/(f_3^8 f_{18}) + 6q^2 f_6^3 f_9^2 f_{18}^2/f_3^7 +
12q^3 f_6^2 f_{18}^5/(f_3^6 f_9)$ with both sides multiplied by $f_1^3 f_3^8 f_9 f_{18}$.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 1, eq. (3) (`integers-2024-A86-lem-1`). -/
public theorem_wanted f2_cube_div_f1_cube_three_dissection :
    𝔣 2 ^ 3 * 𝔣 3 ^ 8 * 𝔣 9 * 𝔣 18 =
      𝔣 1 ^ 3 * (𝔣 3 ^ 7 * 𝔣 6 * 𝔣 9 * 𝔣 18 + 3 * X * 𝔣 6 ^ 4 * 𝔣 9 ^ 6 +
        6 * X ^ 2 * 𝔣 3 * 𝔣 6 ^ 3 * 𝔣 9 ^ 3 * 𝔣 18 ^ 3 +
        12 * X ^ 3 * 𝔣 3 ^ 2 * 𝔣 6 ^ 2 * 𝔣 18 ^ 6)

/-- **The 3-dissection of $1/f_1^3$.** For $k \ge 1$ let $f_k = \prod_{m \ge 1} (1 - q^{km})$ be
the Euler product, an integer power series in $q$. Then
$$
f_3^{12} = f_1^3 f_9^3 \bigl(f_1^6 + 9q f_1^3 f_9^3 + 27q^2 f_9^6\bigr)
$$
and
$$
f_3^{14} f_6^4 f_9^3 f_{18}^6 = f_1^3 \bigl(f_6^6 f_9^{18} + 3q f_3 f_6^5 f_9^{15} f_{18}^3 +
9q^2 f_3^2 f_6^4 f_9^{12} f_{18}^6 + 8q^3 f_3^3 f_6^3 f_9^9 f_{18}^9 +
12q^4 f_3^4 f_6^2 f_9^6 f_{18}^{12} + 16q^6 f_3^6 f_{18}^{18}\bigr).
$$

Since each $f_k$ has constant term $1$ and so is invertible, these are the identities
$1/f_1^3 = (f_9^3/f_3^{12})(f_1^6 + 9q f_1^3 f_9^3 + 27q^2 f_9^6)$ and
$1/f_1^3 = f_6^2 f_9^{15}/(f_3^{14} f_{18}^6) + 3q f_6 f_9^{12}/(f_3^{13} f_{18}^3) +
9q^2 f_9^9/f_3^{12} + 8q^3 f_9^6 f_{18}^3/(f_3^{11} f_6) +
12q^4 f_9^3 f_{18}^6/(f_3^{10} f_6^2) + 16q^6 f_{18}^{12}/(f_3^8 f_6^4 f_9^3)$, multiplied by
$f_1^3 f_3^{12}$ and by $f_1^3 f_3^{14} f_6^4 f_9^3 f_{18}^6$ respectively.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 3, eq. (6) (`integers-2024-A86-lem-3`). -/
public theorem_wanted one_div_f1_cube_three_dissection :
    𝔣 3 ^ 12 = 𝔣 1 ^ 3 * 𝔣 9 ^ 3 *
        (𝔣 1 ^ 6 + 9 * X * 𝔣 1 ^ 3 * 𝔣 9 ^ 3 + 27 * X ^ 2 * 𝔣 9 ^ 6) ∧
      𝔣 3 ^ 14 * 𝔣 6 ^ 4 * 𝔣 9 ^ 3 * 𝔣 18 ^ 6 =
        𝔣 1 ^ 3 * (𝔣 6 ^ 6 * 𝔣 9 ^ 18 + 3 * X * 𝔣 3 * 𝔣 6 ^ 5 * 𝔣 9 ^ 15 * 𝔣 18 ^ 3 +
          9 * X ^ 2 * 𝔣 3 ^ 2 * 𝔣 6 ^ 4 * 𝔣 9 ^ 12 * 𝔣 18 ^ 6 +
          8 * X ^ 3 * 𝔣 3 ^ 3 * 𝔣 6 ^ 3 * 𝔣 9 ^ 9 * 𝔣 18 ^ 9 +
          12 * X ^ 4 * 𝔣 3 ^ 4 * 𝔣 6 ^ 2 * 𝔣 9 ^ 6 * 𝔣 18 ^ 12 +
          16 * X ^ 6 * 𝔣 3 ^ 6 * 𝔣 18 ^ 18)

/-- **Cui–Gu $p$-dissection of $\psi(q)$.** Let $p$ be an odd prime and $q$ a complex number with
$|q| < 1$, let $f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta
function, and let $\psi(q) = f(q, q^3)$. Then
$$
\psi(q) = \sum_{k=0}^{(p-3)/2} q^{k(k+1)/2}
f\bigl(q^{(p^2 + (2k+1)p)/2}, q^{(p^2 - (2k+1)p)/2}\bigr) + q^{(p^2-1)/8} \psi(q^{p^2}),
$$
and $(m^2 + m)/2 \not\equiv (p^2 - 1)/8 \pmod p$ for every integer $m$ with
$0 \le m \le (p - 3)/2$. All the divisions are exact.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 4, eq. (7) (`integers-2024-A86-lem-4`),
quoting S. Cui and N. Gu, *Arithmetic Properties of ℓ-Regular Partitions*, Adv. Appl. Math. 51
(2013), 507–523, Theorem 2.1. -/
public theorem_wanted ramanujanPsi_prime_dissection (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 3) =
        ∑ k ∈ Finset.range ((p - 1) / 2), q ^ (k * (k + 1) / 2) *
            ramanujanThetaRaw (q ^ ((p ^ 2 + (2 * k + 1) * p) / 2))
              (q ^ ((p ^ 2 - (2 * k + 1) * p) / 2)) +
          q ^ ((p ^ 2 - 1) / 8) * ramanujanThetaRaw (q ^ (p ^ 2)) (q ^ (3 * p ^ 2)) ∧
      ∀ m ≤ (p - 3) / 2, ¬ (m ^ 2 + m) / 2 ≡ (p ^ 2 - 1) / 8 [MOD p]

/-- **Cui–Gu $p$-dissection of $f_1$.** Let $p \ge 5$ be a prime, let $s = (p - 1)/6$ if
$p \equiv 1 \pmod 6$ and $s = (-p - 1)/6$ otherwise, and let $q$ be a complex number with
$|q| < 1$. Write $f_k = (q^k; q^k)_\infty = \prod_{m \ge 1} (1 - q^{km})$, let
$f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function, and
let $K$ be the set of integers $k$ with $(1 - p)/2 \le k \le (p - 1)/2$ and $k \ne s$. Then
$$
f_1 = \sum_{k \in K} (-1)^k q^{k(3k+1)/2}
f\bigl(-q^{(3p^2 + (6k+1)p)/2}, -q^{(3p^2 - (6k+1)p)/2}\bigr) +
(-1)^s q^{(p^2-1)/24} f_{p^2}.
$$
All the divisions are exact and all the exponents of $q$ are nonnegative integers.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 5, eq. (8) (`integers-2024-A86-lem-5`),
quoting S. Cui and N. Gu, *Arithmetic Properties of ℓ-Regular Partitions*, Adv. Appl. Math. 51
(2013), 507–523, Theorem 2.2. The same identity is Nayaka, Dharmendra and Mahesh Kumar,
*Divisibility Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80,
Lemma 4, eq. (43) (`integers-2024-A80-lem-4`). -/
public theorem_wanted qPochhammer_prime_dissection (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6)
    (q : ℂ) (hq : ‖q‖ < 1) :
    QPochhammer.qPochhammerInfRaw q q =
      ∑ k ∈ (Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)).erase s,
          (-1 : ℂ) ^ k * q ^ (k * (3 * k + 1) / 2).toNat *
            ramanujanThetaRaw (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
              (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat) +
        (-1 : ℂ) ^ s * q ^ ((p ^ 2 - 1) / 24) *
          QPochhammer.qPochhammerInfRaw (q ^ (p ^ 2)) (q ^ (p ^ 2))

/-- **The 3-dissection of the 2-regular tripartition generating function.** Let $T_2(n)$ be the
number of 2-regular tripartitions of $n$ and $f_k = \prod_{m \ge 1} (1 - q^{km})$. In the ring
$\mathbb{Z}[[q]]$ of integer power series,
$f_1^6 f_3 \sum_{n \ge 0} T_2(3n) q^n = f_1^5 f_2 f_3 + 12 q f_2^2 f_6^5$,
$f_1^8 f_6 \sum_{n \ge 0} T_2(3n + 1) q^n = 3 f_2^4 f_3^5$ and
$f_1^7 \sum_{n \ge 0} T_2(3n + 2) q^n = 6 f_2^3 f_3^2 f_6^2$.

Since each $f_k$ with $k \ge 1$ is invertible in $\mathbb{Z}[[q]]$, these say
$\sum_{n \ge 0} T_2(3n) q^n = f_2 / f_1 + 12 q f_2^2 f_6^5 / (f_1^6 f_3)$,
$\sum_{n \ge 0} T_2(3n + 1) q^n = 3 f_2^4 f_3^5 / (f_1^8 f_6)$ and
$\sum_{n \ge 0} T_2(3n + 2) q^n = 6 f_2^3 f_3^2 f_6^2 / f_1^7$.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 7, eqs. (10)–(12)
(`integers-2024-A86-lem-7`). -/
public theorem_wanted regularTripartitionCount_two_three_dissection :
    𝔣 1 ^ 6 * 𝔣 3 * PowerSeries.mk (fun n => (regularTripartitionCount 2 (3 * n) : ℤ)) =
        𝔣 1 ^ 5 * 𝔣 2 * 𝔣 3 + 12 * X * 𝔣 2 ^ 2 * 𝔣 6 ^ 5 ∧
      𝔣 1 ^ 8 * 𝔣 6 * PowerSeries.mk (fun n => (regularTripartitionCount 2 (3 * n + 1) : ℤ)) =
        3 * 𝔣 2 ^ 4 * 𝔣 3 ^ 5 ∧
      𝔣 1 ^ 7 * PowerSeries.mk (fun n => (regularTripartitionCount 2 (3 * n + 2) : ℤ)) =
        6 * 𝔣 2 ^ 3 * 𝔣 3 ^ 2 * 𝔣 6 ^ 2

/-- **Mod 12 congruences for 2-regular tripartitions.** Let $T_2(n)$ be the number of 2-regular
tripartitions of $n$. For all natural numbers $\alpha$ and $n$, put
$A_\alpha = \sum_{i=0}^{2\alpha+1} 3^{2i}$ and $B_\alpha = \sum_{i=0}^{2\alpha} 3^{2i}$. Then $12$
divides each of $T_2(3^{4\alpha+4} n + A_\alpha + 3^{4\alpha+3})$,
$T_2(3^{4\alpha+4} n + A_\alpha + 2 \cdot 3^{4\alpha+3})$,
$T_2(3^{4\alpha+2} n + B_\alpha + 3^{4\alpha+1})$ and
$T_2(3^{4\alpha+2} n + B_\alpha + 2 \cdot 3^{4\alpha+1})$.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 3, eqs. (31)–(34)
(`integers-2024-A86-thm-3`). -/
public theorem_wanted regularTripartitionCount_two_mod_twelve (α n : ℕ) :
    12 ∣ regularTripartitionCount 2
        (3 ^ (4 * α + 4) * n + ∑ i ∈ Finset.range (2 * α + 2), 3 ^ (2 * i) +
          3 ^ (4 * α + 3)) ∧
      12 ∣ regularTripartitionCount 2
        (3 ^ (4 * α + 4) * n + ∑ i ∈ Finset.range (2 * α + 2), 3 ^ (2 * i) +
          2 * 3 ^ (4 * α + 3)) ∧
      12 ∣ regularTripartitionCount 2
        (3 ^ (4 * α + 2) * n + ∑ i ∈ Finset.range (2 * α + 1), 3 ^ (2 * i) +
          3 ^ (4 * α + 1)) ∧
      12 ∣ regularTripartitionCount 2
        (3 ^ (4 * α + 2) * n + ∑ i ∈ Finset.range (2 * α + 1), 3 ^ (2 * i) +
          2 * 3 ^ (4 * α + 1))

/-- **The 3-dissection of the generating function of 3-regular tripartitions.** Let $T_3(n)$ be
the number of $3$-regular tripartitions of $n$, and for $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler product. Then, as integer power series in $q$,
$$
f_1^{11} f_2^4 f_3^3 f_6^6 \sum_{n \ge 0} T_3(3n) q^n =
f_2^6 f_3^{18} + 8q f_1^3 f_2^3 f_3^9 f_6^9 + 16q^2 f_1^6 f_6^{18},
$$
$$
f_1^{10} f_2^2 f_6^3 \sum_{n \ge 0} T_3(3n + 1) q^n = 3 f_2^3 f_3^{12} + 12q f_1^3 f_3^3 f_6^9
$$
and
$$
f_1^9 \sum_{n \ge 0} T_3(3n + 2) q^n = 9 f_3^9.
$$

Since each $f_k$ has constant term $1$ and so is invertible, these are the identities
$\sum T_3(3n) q^n = f_2^2 f_3^{15}/(f_1^{11} f_6^6) + 8q f_3^6 f_6^3/(f_1^8 f_2) +
16q^2 f_6^{12}/(f_1^5 f_2^4 f_3^3)$,
$\sum T_3(3n + 1) q^n = 3 f_2 f_3^{12}/(f_1^{10} f_6^3) + 12q f_3^3 f_6^6/(f_1^7 f_2^2)$ and
$\sum T_3(3n + 2) q^n = 9 f_3^9/f_1^9$ with the denominators cleared.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 4, eqs. (49)–(51)
(`integers-2024-A86-thm-4`). -/
public theorem_wanted regularTripartitionCount_three_three_dissection :
    𝔣 1 ^ 11 * 𝔣 2 ^ 4 * 𝔣 3 ^ 3 * 𝔣 6 ^ 6 *
          PowerSeries.mk (fun n => (regularTripartitionCount 3 (3 * n) : ℤ)) =
        𝔣 2 ^ 6 * 𝔣 3 ^ 18 + 8 * X * 𝔣 1 ^ 3 * 𝔣 2 ^ 3 * 𝔣 3 ^ 9 * 𝔣 6 ^ 9 +
          16 * X ^ 2 * 𝔣 1 ^ 6 * 𝔣 6 ^ 18 ∧
      𝔣 1 ^ 10 * 𝔣 2 ^ 2 * 𝔣 6 ^ 3 *
          PowerSeries.mk (fun n => (regularTripartitionCount 3 (3 * n + 1) : ℤ)) =
        3 * 𝔣 2 ^ 3 * 𝔣 3 ^ 12 + 12 * X * 𝔣 1 ^ 3 * 𝔣 3 ^ 3 * 𝔣 6 ^ 9 ∧
      𝔣 1 ^ 9 * PowerSeries.mk (fun n => (regularTripartitionCount 3 (3 * n + 2) : ℤ)) =
        9 * 𝔣 3 ^ 9

end

end MetaMathlibExt
