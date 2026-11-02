/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Intersections in pairs of words

Statements from Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*,
INTEGERS 24 (2024), Article A107.

A word of length `n` over the alphabet `[k]` is a map `Fin n → Fin k`; a pair `(u, v)` is
non-intersecting when no letter occurs in both, and the overlap statistic (tracked by `q`) is the
number of positions of `v` whose letter occurs in `u`. Weakly decreasing words are `Antitone`
maps. The paper's generating functions run over pairs of non-empty words (`x^n y^r`, `n, r ≥ 1`).
A two-variable generating function that factors as `A(x) B(y)` is stated coefficientwise:
`[x^n y^r] A(x)B(y) = [x^n]A · [y^r]B`, with `A`, `B` in `ℚ⟦X⟧`; `q` is a rational parameter
(an identity of polynomials in `q` holds iff it holds for every `q : ℚ`); Corollary 4 is stated in
`MvPowerSeries (Fin 2) ℚ` with `x = X 0`, `y = X 1`. `S_{n,j}` is `Nat.stirlingSecond n j`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Non-intersecting pairs of words.** Fix natural numbers $k$, $n \ge 1$ and $r \ge 1$, and call
a pair of words over an alphabet of $k$ letters non-intersecting when no letter occurs in both.
Write $[x^m] F$ for the coefficient of $x^m$ in a formal power series $F$ over $\mathbb{Q}$ and
$S(m, j)$ for the Stirling numbers of the second kind. Let $N$ be the number of non-intersecting
pairs $(u, v)$ with $u$ of length $n$ and $v$ of length $r$. Then
$N = \sum_{j=1}^{k-1} \binom{k}{j} \,
[x^n]\Bigl(j! \, x^j \bigl(\prod_{i=1}^{j} (1 - i x)\bigr)^{-1}\Bigr) \,
[x^r]\bigl((k-j) x \, (1 - (k-j) x)^{-1}\bigr)$
and
$N = \sum_{j=1}^{k-1} \binom{k}{j} \, j! \, S(n, j) \,
[x^r]\bigl((k-j) x \, (1 - (k-j) x)^{-1}\bigr)$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Theorem 1 (`integers-2024-A107-thm-1`). -/
public theorem_wanted nonIntersectingWordPairs_card_eq_coeff (k n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) =
        ∑ j ∈ Finset.Icc 1 (k - 1), (k.choose j : ℚ) *
          coeff n ((j.factorial : ℚ⟦X⟧) * X ^ j * (∏ i ∈ Finset.Icc 1 j, (1 - (i : ℚ⟦X⟧) * X))⁻¹) *
          coeff r (((k - j : ℕ) : ℚ⟦X⟧) * X * (1 - ((k - j : ℕ) : ℚ⟦X⟧) * X)⁻¹) ∧
      (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) =
        ∑ j ∈ Finset.Icc 1 (k - 1), (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j *
          coeff r (((k - j : ℕ) : ℚ⟦X⟧) * X * (1 - ((k - j : ℕ) : ℚ⟦X⟧) * X)⁻¹)

/-- **Generating function of non-intersecting pairs of words of equal length.** Let $k$ be a
natural number, let $S(n, j)$ denote the Stirling numbers of the second kind, and for $n \ge 1$ let
$h(n)$ be the number of pairs $(u, v)$ of words of length $n$ over an alphabet of $k$ letters such
that no letter occurs in both. Then, as formal power series over $\mathbb{Q}$,
$\sum_{n \ge 1} h(n) x^n = \sum_{n \ge 0} \sum_{j=1}^{k-1} \binom{k}{j} \, j! \, S(n, j) \,
(k-j)^n x^n$.

The constant term on the right is $0$ because $S(0, j) = 0$ for $j \ge 1$: the empty pair is not
counted.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 1 (`integers-2024-A107-cor-1`). -/
public theorem_wanted nonIntersectingWordPairs_sameLength_generatingFunction (k : ℕ) :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else
        (((Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))).filter fun p => Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ)) =
      PowerSeries.mk fun n => ∑ j ∈ Finset.Icc 1 (k - 1),
        (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j * ((k - j : ℕ) : ℚ) ^ n

/-- **Non-intersecting pairs of words of equal length.** Let $S(n, j)$ denote the Stirling numbers
of the second kind. For natural numbers $k$ and $n \ge 1$, the number of pairs $(u, v)$ of words
of length $n$ over an alphabet of $k$ letters such that no letter occurs in both $u$ and $v$ is
$\sum_{j=1}^{k-1} \binom{k}{j} \, j! \, S(n, j) \, (k-j)^n$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 2 (`integers-2024-A107-cor-2`). -/
public theorem_wanted nonIntersectingWordPairs_sameLength_card (k n : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset ((Fin n → Fin k) × (Fin n →
        Fin k))).filter fun p => Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card =
      ∑ j ∈ Finset.Icc 1 (k - 1), k.choose j * j.factorial * Nat.stirlingSecond n j * (k - j) ^ n

/-- **Overlap statistic on pairs of words.** Fix natural numbers $k$, $n \ge 1$, $r \ge 1$ and a
rational number $q$. For words $u$ and $v$ over an alphabet of $k$ letters, the overlap of
$(u, v)$ is the number of positions of $v$ whose letter occurs in $u$. Write $[x^m] F$ for the
coefficient of $x^m$ in a formal power series $F$ over $\mathbb{Q}$, $S(m, j)$ for the Stirling
numbers of the second kind, and $c_j = qj + k - j$. Then the sum of $q^{\text{overlap}}$ over all
pairs $(u, v)$ with $u$ of length $n$ and $v$ of length $r$ equals
$\sum_{j=1}^{k} \binom{k}{j} \, [x^r]\bigl(c_j x \, (1 - c_j x)^{-1}\bigr) \, j! \, S(n, j)$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Theorem 2 (`integers-2024-A107-thm-2`). -/
public theorem_wanted wordPairs_overlap_sum_eq_coeff (k n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℚ) :
    ∑ p ∈ (Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))),
        q ^ (Finset.univ.filter fun i => p.2 i ∈ Finset.univ.image p.1).card =
      ∑ j ∈ Finset.Icc 1 k, (k.choose j : ℚ) *
        coeff r (PowerSeries.C (q * j + (k - j : ℕ)) * X *
          (1 - PowerSeries.C (q * j + (k - j : ℕ)) * X)⁻¹) *
        (j.factorial * Nat.stirlingSecond n j)

/-- **Overlap statistic on pairs of words of equal length.** Fix natural numbers $k$ and $n \ge 1$
and a rational number $q$. For words $u$ and $v$ over an alphabet of $k$ letters, the overlap of
$(u, v)$ is the number of positions of $v$ whose letter occurs in $u$. Let $S(n, j)$ denote the
Stirling numbers of the second kind. Then the sum of $q^{\text{overlap}}$ over all pairs $(u, v)$
of words of length $n$ equals $\sum_{j=1}^{k} \binom{k}{j} \, j! \, S(n, j) \, (qj + k - j)^n$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 3 (`integers-2024-A107-cor-3`). -/
public theorem_wanted wordPairs_sameLength_overlap_sum (k n : ℕ) (hn : 1 ≤ n) (q : ℚ) :
    ∑ p ∈ (Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))),
        q ^ (Finset.univ.filter fun i => p.2 i ∈ Finset.univ.image p.1).card =
      ∑ j ∈ Finset.Icc 1 k,
        (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j * (q * j + (k - j : ℕ)) ^ n

/-- **Non-intersecting pairs of weakly decreasing words.** Fix natural numbers $k$, $n \ge 1$ and
$r \ge 1$, and order an alphabet of $k$ letters. Write $[x^m] F$ for the coefficient of $x^m$ in a
formal power series $F$ over $\mathbb{Q}$. The number of pairs $(u, v)$ of weakly decreasing words
over this alphabet, $u$ of length $n$ and $v$ of length $r$, such that no letter occurs in both is
$\sum_{j=1}^{k-1} \binom{k}{j} \, [x^n]\bigl(x^j (1-x)^{-j}\bigr) \,
[x^r]\bigl((1-x)^{-(k-j)} - 1\bigr)$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Theorem 3 (`integers-2024-A107-thm-3`). -/
public theorem_wanted weaklyDecreasingNonIntersectingPairs_card_eq_coeff (k n r : ℕ) (hn : 1 ≤ n)
    (hr : 1 ≤ r) :
    (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Antitone p.1 ∧
        Antitone p.2 ∧ Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) =
      ∑ j ∈ Finset.Icc 1 (k - 1), (k.choose j : ℚ) * coeff n (X ^ j * ((1 - X) ^ j)⁻¹ : ℚ⟦X⟧) *
        coeff r ((((1 - X) ^ (k - j))⁻¹ - 1 : ℚ⟦X⟧))

/-- **Generating function of non-intersecting pairs of weakly decreasing words.** Let $k$ be a
natural number and order an alphabet of $k$ letters. In the ring of formal power series in $x$
and $y$ over $\mathbb{Q}$ let
$f(x, y) = \bigl(x (1-x)^{-1} + (1-y)^{-1}\bigr)^k - (1-x)^{-k} - (1-y)^{-k} + 1$.
Then for all natural numbers $n$ and $r$, the coefficient of $x^n y^r$ in $f$ is $0$ if $n = 0$
or $r = 0$, and otherwise equals the number of pairs $(u, v)$ of weakly decreasing words over this
alphabet, $u$ of length $n$ and $v$ of length $r$, such that no letter occurs in both.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 4 (`integers-2024-A107-cor-4`). -/
public theorem_wanted weaklyDecreasingNonIntersectingPairs_generatingFunction (k n r : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 r)
        ((MvPowerSeries.X 0 * (1 - MvPowerSeries.X 0)⁻¹ + (1 - MvPowerSeries.X 1)⁻¹) ^ k -
          ((1 - MvPowerSeries.X 0)⁻¹) ^ k - ((1 - MvPowerSeries.X 1)⁻¹) ^ k + 1 :
          MvPowerSeries (Fin 2) ℚ) =
      if 1 ≤ n ∧ 1 ≤ r then (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r →
          Fin k))).filter fun p => Antitone p.1 ∧ Antitone p.2 ∧
          Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) else 0

/-- **Non-intersecting pairs of weakly decreasing words of equal length.** For natural numbers $k$
and $n \ge 1$, the number of pairs $(u, v)$ of weakly decreasing words of length $n$ over an
ordered alphabet of $k$ letters such that no letter occurs in both is
$\sum_{j=1}^{k-1} \binom{k}{j} \binom{n-1}{j-1} \binom{n+k-j-1}{n}$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 5 (`integers-2024-A107-cor-5`). -/
public theorem_wanted weaklyDecreasingNonIntersectingPairs_sameLength_card (k n : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))).filter fun p => Antitone p.1 ∧
        Antitone p.2 ∧ Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card =
      ∑ j ∈ Finset.Icc 1 (k - 1), k.choose j * (n - 1).choose (j - 1) * (n + k - j - 1).choose n

/-- **Overlap statistic on pairs of weakly decreasing words.** Fix natural numbers $k$, $n \ge 1$,
$r \ge 1$ and a rational number $q$, and order an alphabet of $k$ letters. For words $u$ and $v$
over this alphabet, the overlap of $(u, v)$ is the number of positions of $v$ whose letter occurs
in $u$. Write $[x^m] F$ for the coefficient of $x^m$ in a formal power series $F$ over
$\mathbb{Q}$. Let $T$ be the sum of $q^{\text{overlap}}$ over all pairs $(u, v)$ of weakly
decreasing words, $u$ of length $n$ and $v$ of length $r$. Then
$T = \sum_{j=1}^{k} \binom{k}{j} \, [x^n]\bigl(x^j (1-x)^{-j}\bigr) \,
[x^r]\Bigl((1-x)^{-(k-j)} - 1 + (1-x)^{-(k-j)} \sum_{m \ge 1} \binom{m+j-1}{m} q^m x^m\Bigr)$
and
$T = \sum_{j=1}^{k} \binom{k}{j} \, [x^n]\bigl(x^j (1-x)^{-j}\bigr) \,
[x^r]\bigl(-1 + (1-x)^{-(k-j)} (1 - qx)^{-j}\bigr)$.

The paper prints these sums over $j$ with upper limit $k - 1$, which omits the pairs whose first
word uses all $k$ letters ($j = k$, which Theorem 2 includes): for $k = 1$ and $n = r = 1$ the
only pair contributes $q$, while the printed sum is empty.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Theorem 4 (`integers-2024-A107-thm-4`). -/
public theorem_wanted weaklyDecreasingPairs_overlap_sum_eq_coeff (k n r : ℕ) (hn : 1 ≤ n)
    (hr : 1 ≤ r) (q : ℚ) :
    ∑ p ∈ ((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Antitone p.1 ∧
        Antitone p.2), q ^ (Finset.univ.filter fun i => p.2 i ∈ Finset.univ.image p.1).card =
        ∑ j ∈ Finset.Icc 1 k, (k.choose j : ℚ) * coeff n (X ^ j * ((1 - X) ^ j)⁻¹ : ℚ⟦X⟧) *
          coeff r ((((1 - X) ^ (k - j))⁻¹ - 1 + ((1 - X) ^ (k - j))⁻¹ *
            PowerSeries.mk fun m => if m = 0 then 0 else ((m + j - 1).choose m : ℚ) *
                q ^ m : ℚ⟦X⟧)) ∧
      ∑ p ∈ ((Finset.univ : Finset ((Fin n → Fin k) × (Fin r →
          Fin k))).filter fun p => Antitone p.1 ∧
          Antitone p.2), q ^ (Finset.univ.filter fun i => p.2 i ∈ Finset.univ.image p.1).card =
        ∑ j ∈ Finset.Icc 1 k, (k.choose j : ℚ) * coeff n (X ^ j * ((1 - X) ^ j)⁻¹ : ℚ⟦X⟧) *
          coeff r ((-1 + ((1 - X) ^ (k - j))⁻¹ * ((1 - PowerSeries.C q * X) ^ j)⁻¹ : ℚ⟦X⟧))

end

end MetaMathlibExt
