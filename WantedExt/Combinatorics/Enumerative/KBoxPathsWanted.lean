/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.KBoxReturnGF

/-!
# `k`-box paths: a subfamily of skew Dyck paths related to `k`-ary trees

Statements from Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to
`k`-ary Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4
(arXiv:2306.15778). Skew Dyck paths are words over `{U, D, L}` that avoid the
factors `UL` and `LU`, have as many `U`s as `D`s and `L`s together, and have no
prefix with more `D`s and `L`s than `U`s; the semilength is the number of `U`s.
A `k`-box path of size `n` (`k ≥ 1`) is a skew Dyck path of semilength
`(k+2)n - 1` with exactly `n` factors `U D^k L`. A `k`-Dyck path is a word over
`Bool` (`true` for `U = (1,1)`, `false` for `D^{(k)} = (k,-k)`), and an
augmented `k`-Dyck path replaces each `D^{(k)}` by `U D^{k-1} L D`.
-/

namespace MetaMathlibExt

@[expose] public section

open SkewDyckStep

/-- The variable `x` of the bivariate generating functions. -/
local notation "𝒙" => (PowerSeries.X : PowerSeries (Polynomial ℤ))
/-- The variable `t` of the bivariate generating functions, a constant in `ℤ[t]`. -/
local notation "𝒕" => PowerSeries.C (Polynomial.X : Polynomial ℤ)

/-- **Structure of $k$-box paths.** Let $k \ge 1$ and $n \ge 1$. For a list
$a = (a_1, \dots, a_n)$ of natural numbers write
$w_k(a) = U^{a_1} D^k L D \cdots U^{a_{n-1}} D^k L D\, U^{a_n} D^k L$. Every $k$-box path of
size $n$ equals $w_k(a)$ for some list $a$ of $n$ positive integers. Conversely, if $a$ is a
list of $n$ positive integers with $a_1 + \cdots + a_n = (k+2)n - 1$ and no prefix of $w_k(a)$
has more $D$s and $L$s together than $U$s, then $w_k(a)$ is a $k$-box path of size $n$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 2
(`jis-2024-24.2.4-lem-2`). -/
public theorem_wanted kBoxPaths_structure {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∀ w ∈ kBoxPaths k n, ∃ a : List ℕ, a.length = n ∧ (∀ x ∈ a, 0 < x) ∧ w = boxWord k a) ∧
    ∀ a : List ℕ, a.length = n → (∀ x ∈ a, 0 < x) → a.sum = (k + 2) * n - 1 →
      (∀ i ≤ (boxWord k a).length, ((boxWord k a).take i).count D +
        ((boxWord k a).take i).count L ≤ ((boxWord k a).take i).count U) →
      boxWord k a ∈ kBoxPaths k n

/-- **Decomposition of $k$-box paths.** Let $k \ge 1$. A word $w$ in the steps $U$, $D$, $L$ is a
$k$-box path of some size $n \ge 1$ if and only if $w = \mu_1 U \mu_2 U \cdots \mu_{k+1} U D^k L$
for some augmented $(k+1)$-Dyck paths $\mu_1, \ldots, \mu_{k+1}$, each of some size.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 4
(`jis-2024-24.2.4-lem-4`). -/
public theorem_wanted kBoxPaths_decomposition {k : ℕ} (hk : 1 ≤ k) (w : List SkewDyckStep) :
    (∃ n, 1 ≤ n ∧ w ∈ kBoxPaths k n) ↔
      ∃ μ : Fin (k + 1) → List SkewDyckStep, (∀ i, ∃ m, μ i ∈ augmentedKDyckPaths (k + 1) m) ∧
        w = (List.ofFn fun i => μ i ++ [U]).flatten ++ List.replicate k D ++ [L]

/-- **Number of $k$-box paths of size $n$.** Let $k \ge 1$ and $n \ge 1$, and let $f_{k,n}$ be
the number of $k$-box paths of size $n$. Then
$$
((k+2)n - 1) \, f_{k,n} = \binom{(k+2)n - 1}{n},
$$
and if moreover $n \ge 2$, then
$$
(n - 1) \, f_{k,n} = (k+1) \binom{(k+2)n - 2}{n - 2}.
$$

The source also identifies $f_{k,n}$ with the number of $(k+1)$-tuples of $(k+2)$-ary trees
with $n - 1$ nodes; that identification is not part of this statement.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 5
(`jis-2024-24.2.4-thm-5`). -/
public theorem_wanted card_kBoxPaths {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ((k + 2) * n - 1) * (kBoxPaths k n).card = ((k + 2) * n - 1).choose n ∧
      (2 ≤ n → (n - 1) * (kBoxPaths k n).card = (k + 1) * ((k + 2) * n - 2).choose (n - 2))

/-- **Counting tailed $k$-box paths.** Let $k \ge 1$ and $n \ge 1$, and let $T$ be the number of
$k$-box paths of size $n$ that end with $U^{k+1} D^k L$. Then
$((k+2)(n-1)+1) \cdot T = \binom{(k+2)(n-1)+1}{n-1}$, and if $n \ge 2$ then also
$(n-1) \cdot T = \binom{(k+2)(n-1)}{n-2}$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Proposition 7
(`jis-2024-24.2.4-prop-7`). -/
public theorem_wanted card_tailed_kBoxPaths {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ((k + 2) * (n - 1) + 1) *
        ((kBoxPaths k n).filter fun w =>
          List.replicate (k + 1) U ++ List.replicate k D ++ [L] <:+ w).card =
      ((k + 2) * (n - 1) + 1).choose (n - 1) ∧
    (2 ≤ n → (n - 1) * ((kBoxPaths k n).filter fun w =>
          List.replicate (k + 1) U ++ List.replicate k D ++ [L] <:+ w).card =
      ((k + 2) * (n - 1)).choose (n - 2))

/-- **Number of $k$-box paths with $j$ returns.** Let $k \ge 1$ and $1 \le j \le n$, and let
$r_{k,n,j}$ be the number of $k$-box paths of size $n$ with exactly $j$ returns. Then
$$
((k+2)n - j - 1) \, r_{k,n,j} = (j(k+1) - 1) \binom{(k+2)n - j - 1}{n - j},
$$
and if moreover $j < n$, then
$$
(n - j) \, r_{k,n,j} = (j(k+1) - 1) \binom{(k+2)n - j - 2}{n - j - 1}.
$$

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 9
(`jis-2024-24.2.4-thm-9`). -/
public theorem_wanted card_kBoxPaths_returns {k n j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hjn : j ≤ n) :
    ((k + 2) * n - j - 1) * ((kBoxPaths k n).filter fun w => skewReturns w = j).card =
        (j * (k + 1) - 1) * ((k + 2) * n - j - 1).choose (n - j) ∧
      (j < n → (n - j) * ((kBoxPaths k n).filter fun w => skewReturns w = j).card =
        (j * (k + 1) - 1) * ((k + 2) * n - j - 2).choose (n - j - 1))

/-- **Mean and variance of the number of returns of $k$-box paths.** Let $k \ge 1$ and $n \ge 1$,
and let $R(\mu)$ be the number of returns (steps ending on the $x$-axis) of a path $\mu$. The
average of $R$ over the $k$-box paths of size $n$ is
$$\frac{(k+2)((k+2)n-1)}{(k+1)((k+1)n+1)},$$
and the average of $R^2$ over these paths minus the square of the average of $R$ is
$$\frac{(k+2)((k+2)n-1)((2k+1)(k+1)n-2)(n-1)}{(k+1)^2((k+1)n+1)^2((k+1)n+2)}.$$

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Corollary 11
(`jis-2024-24.2.4-cor-11`). -/
public theorem_wanted kBoxPaths_returns_mean_variance {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ)) / (kBoxPaths k n).card =
        ((k + 2) * ((k + 2) * n - 1) : ℚ) / ((k + 1) * ((k + 1) * n + 1)) ∧
      (∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ) ^ 2) / (kBoxPaths k n).card -
          ((∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ)) / (kBoxPaths k n).card) ^ 2 =
        ((k + 2) * ((k + 2) * n - 1) * ((2 * k + 1) * (k + 1) * n - 2) * (n - 1) : ℚ) /
          ((k + 1) ^ 2 * ((k + 1) * n + 1) ^ 2 * ((k + 1) * n + 2))

/-- **Long-ascent functional equations for $k$-box paths.** Let $\acute F_k(t, x)$ be the
long-ascent generating function of $k$-box paths and $\acute G_k(t, x)$ that of augmented
$k$-Dyck paths, including the empty path, both in $\mathbb{Z}[t][[x]]$. Then for every $k \ge 1$
$$
\acute F_k = x \, \acute G_{k+1}^{k} \, (\acute G_{k+1} - 1 + t),
$$
and for every $k \ge 2$
$$
\acute G_k = 1 + x \, \acute G_k^{k} \, (\acute G_k - 1 + t).
$$

The source's displayed sum for $\acute G_k$ omits the empty path; here $\acute G_k$ includes it
(constant term $1$), as both equations require.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 12
(`jis-2024-24.2.4-lem-12`). -/
public theorem_wanted kBoxLongAscentGF_functional_equations :
    (∀ k : ℕ, 1 ≤ k → kBoxLongAscentGF k =
      𝒙 * augmentedKDyckLongAscentGF (k + 1) ^ k *
        (augmentedKDyckLongAscentGF (k + 1) - 1 + 𝒕)) ∧
    ∀ k : ℕ, 2 ≤ k → augmentedKDyckLongAscentGF k =
      1 + 𝒙 * augmentedKDyckLongAscentGF k ^ k * (augmentedKDyckLongAscentGF k - 1 + 𝒕)

/-- **Number of $k$-box paths with $j$ long ascents.** Let $k \ge 1$, $n \ge 1$ and $j \ge 1$,
and let $a_{k,n,j}$ be the number of $k$-box paths of size $n$ with exactly $j$ long ascents.
Then
$$
j \, a_{k,n,j} = \binom{(k+1)n - 2}{j - 1} \binom{n - 1}{j - 1}.
$$
For $j > n$ both sides vanish.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 13
(`jis-2024-24.2.4-thm-13`). -/
public theorem_wanted card_kBoxPaths_longAscents {k n j : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hj : 1 ≤ j) :
    j * ((kBoxPaths k n).filter fun w => skewLongAscents w = j).card =
      ((k + 1) * n - 2).choose (j - 1) * (n - 1).choose (j - 1)

/-- **Second polygonal numbers count box paths with two long ascents.** Let $K \ge 4$ and
$n \ge 1$. Then $n\bigl((K-2)n + (K-4)\bigr)$ is twice the number of $(K-3)$-box paths of size
$n + 1$ with exactly two long ascents (maximal runs of at least two $U$ steps). Equivalently,
the $n$th second $K$-gonal number $n\bigl((K-2)n + (K-4)\bigr)/2$, the $K$-gonal formula
$m\bigl((K-2)m - (K-4)\bigr)/2$ at $m = -n$, equals this number of paths.

The source states this for $K \ge 3$, where the case $K = 3$ uses its convention for $0$-box
paths.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 15
(`jis-2024-24.2.4-thm-15`). -/
public theorem_wanted second_polygonal_eq_card_kBoxPaths_two_longAscents {K n : ℕ}
    (hK : 4 ≤ K) (hn : 1 ≤ n) :
    n * ((K - 2) * n + (K - 4)) =
      2 * ((kBoxPaths (K - 3) (n + 1)).filter fun w => skewLongAscents w = 2).card

/-- **Long ascents of box paths: sum and sum of squares.** Let $k \ge 1$ and $n \ge 1$, let
$B_n^{(k)}$ be the set of $k$-box paths of size $n$, and for a path $w$ let $\mathrm{la}(w)$ be
its number of long ascents. Then
$$\sum_{w \in B_n^{(k)}} \mathrm{la}(w) = \binom{(k+2)n-3}{n-1}$$
and
$$\bigl((k+2)n-3\bigr) \sum_{w \in B_n^{(k)}} \mathrm{la}(w)^2 =
\bigl((k+1)n^2-n-1\bigr) \binom{(k+2)n-3}{n-1}.$$

The source states the second identity divided by $(k+2)n-3$, that is, with the sum of
$\mathrm{la}(w)^2$ equal to $\frac{(k+1)n^2-n-1}{(k+2)n-3}\binom{(k+2)n-3}{n-1}$; at $k = n = 1$
the cleared form reads $0 = 0$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 17
(`jis-2024-24.2.4-lem-17`). -/
public theorem_wanted sum_kBoxPaths_longAscents {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ∑ w ∈ kBoxPaths k n, skewLongAscents w = ((k + 2) * n - 3).choose (n - 1) ∧
      ((k + 2) * n - 3) * ∑ w ∈ kBoxPaths k n, skewLongAscents w ^ 2 =
        ((k + 1) * n ^ 2 - n - 1) * ((k + 2) * n - 3).choose (n - 1)

/-- **Mean and variance of long ascents in $k$-box paths.** Let $k \ge 1$ and $n \ge 1$. Over the
$k$-box paths of size $n$, taken with equal weight, the mean number of long ascents is
$$
\frac{n((k+1)n-1)}{(k+2)n-2}
$$
and the variance (the mean of the square minus the square of the mean) is
$$
\frac{((k+1)n-1)((k+1)n-2)\,n(n-1)}{((k+2)n-2)^2\,((k+2)n-3)}.
$$

When $k = n = 1$ the variance is $0$, and the last fraction reads $0/0$, which is taken to be $0$.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Proposition 18
(`jis-2024-24.2.4-prop-18`). -/
public theorem_wanted kBoxPaths_longAscents_mean_variance {k n : ℕ} (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ w ∈ kBoxPaths k n, (skewLongAscents w : ℚ)) / (kBoxPaths k n).card =
        (n * ((k + 1) * n - 1) : ℚ) / ((k + 2) * n - 2) ∧
      (∑ w ∈ kBoxPaths k n, (skewLongAscents w : ℚ) ^ 2) / (kBoxPaths k n).card -
          ((∑ w ∈ kBoxPaths k n, (skewLongAscents w : ℚ)) / (kBoxPaths k n).card) ^ 2 =
        (((k + 1) * n - 1) * ((k + 1) * n - 2) * n * (n - 1) : ℚ) /
          (((k + 2) * n - 2) ^ 2 * ((k + 2) * n - 3))

end

end MetaMathlibExt
