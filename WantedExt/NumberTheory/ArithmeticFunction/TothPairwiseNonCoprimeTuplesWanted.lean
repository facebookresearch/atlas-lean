/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Fintype.Pi
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Tóth, k-tuples with pairwise non-coprime components — wishlist

Statement-only records for László Tóth's JIS 27 (2024) paper. A coprimality
graph on the vertex set `Fin k` is encoded by its edge set
`E : Finset (Fin k × Fin k)` with `e.1 < e.2` for every `e ∈ E`, matching the
paper's `E ⊆ V^{(2)} = {{i, j} : 1 ≤ i < j ≤ k}`. Sums over
`n₁, …, n_k ≤ x` are taken over `Fintype.piFinset (fun _ => Finset.Icc 1 N)`
for natural `N ≥ 2`; since `⌊x⌋^k = x^k + O(x^{k-1})`, this is equivalent to
the real-`x` statements.

Theorem 2 of the paper (Ushiroya's mean-value theorem) is already in
`MathlibExt/NumberTheory/ArithmeticFunction/WintnerMeanValueMultivariable.lean`.
`MathlibExt/NumberTheory/ArithmeticFunction/EulerProductMeanValue.lean` proves Theorem 3
only under coordinatewise multiplicativity, which is stronger than the source's; the
source-strength Theorem 3 is `euler_product_mean_value_of_coprime_prod` below.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- **Coprimality indicator of a graph.** Let $E$ be a set of ordered pairs $(i, j)$ of indices in
$\{0, \dots, k-1\}$, the edge set of a graph $G$ on these $k$ vertices. For
$n = (n_0, \dots, n_{k-1}) \in \mathbb{N}^k$, the coprimality indicator $\delta_G(n)$ is the
natural number $1$ if $\gcd(n_i, n_j) = 1$ for every $(i, j) \in E$, and $0$ otherwise.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, display (def_delta_G). -/
public def coprimalityIndicator {k : ℕ} (E : Finset (Fin k × Fin k))
    (n : Fin k → ℕ) : ℕ :=
  if ∀ e ∈ E, Nat.Coprime (n e.1) (n e.2) then 1 else 0

/-- **Coprimality indicator of the empty graph.** Let $k \in \mathbb{N}$ and let $G$ be the graph
on $k$ vertices with no edges, and let $\delta_G$ be its coprimality indicator. Then
$\delta_G(n) = 1$ for every $n = (n_0, \dots, n_{k-1}) \in \mathbb{N}^k$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, remark after display (def_delta_G). -/
public theorem coprimalityIndicator_empty {k : ℕ} (n : Fin k → ℕ) :
    coprimalityIndicator (∅ : Finset (Fin k × Fin k)) n = 1 := by
  simp [coprimalityIndicator]

/-- **Coprimality indicator of a single edge: examples.** Let $G$ be the graph on the two
vertices $0, 1$ with the single edge $(0, 1)$, with coprimality indicator $\delta_G$. Then
$\delta_G(2, 3) = 1$ and $\delta_G(2, 4) = 0$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, display (def_delta_G). -/
public theorem coprimalityIndicator_small_values :
    coprimalityIndicator ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)) ![2, 3] = 1 ∧
      coprimalityIndicator ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2))
        ![2, 4] = 0 := by
  decide

/-- **Number of coprime pairs.** For $n = (n_0, \dots, n_{k-1}) \in \mathbb{N}^k$, the number of
coprime pairs of $n$ is the number of index pairs $(i, j)$ with $0 \le i < j < k$ and
$\gcd(n_i, n_j) = 1$.

In the paper's notation, $\beta_r(n) = 1$ exactly when this count is $r$, $\beta'_r(n) = 1$
exactly when it is at least $r$, and $\beta = \beta_0$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, displays (def_beta), (def_beta_exact), (def_beta_least). -/
public def coprimePairCount {k : ℕ} (n : Fin k → ℕ) : ℕ :=
  ((univ.filter fun e : Fin k × Fin k => e.1 < e.2).filter
    fun e => Nat.Coprime (n e.1) (n e.2)).card

/-- **Number of coprime pairs: examples.** The triple $(2, 3, 4)$ has exactly two coprime pairs
of components, and the triple $(6, 10, 15)$ has none, that is, its components are pairwise
non-coprime.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, displays (def_beta) and (def_beta_exact). -/
public theorem coprimePairCount_small_values :
    coprimePairCount ![2, 3, 4] = 2 ∧ coprimePairCount ![6, 10, 15] = 0 := by
  decide

/-- **Coprimality density of a graph.** Let $k$ be a natural number and let $E$ be a set of ordered
pairs $(a, b)$ of vertices in $\{1, \dots, k\}$, the edge set of a graph $G$. For $F \subseteq E$
let $v(F)$ be the number of distinct vertices that occur in some pair of $F$. The coprimality
density of $G$ is the real number
$$A_G = \prod_p \sum_{F \subseteq E} \frac{(-1)^{|F|}}{p^{v(F)}},$$
the product running over all primes $p$.

When every edge $(a, b)$ has $a < b$, this is the Arias de Reyna–Heyman form of the asymptotic
density of the $k$-tuples $(n_1, \dots, n_k)$ of positive integers with $\gcd(n_a, n_b) = 1$ for
every edge $(a, b)$ of $G$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1, display (A_G_version). -/
public noncomputable def coprimalityDensity {k : ℕ} (E : Finset (Fin k × Fin k)) : ℝ :=
  ∏' p : Nat.Primes, ∑ F ∈ E.powerset,
    (-1 : ℝ) ^ F.card /
      ((p : ℕ) : ℝ) ^ (univ.filter fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i).card

/-- **The coprimality density of the empty graph is $1$.** For every natural number $k$, the
coprimality density of the graph on $\{1, \dots, k\}$ with no edges equals $1$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1, display (A_G_version). -/
public theorem coprimalityDensity_empty (k : ℕ) :
    coprimalityDensity (∅ : Finset (Fin k × Fin k)) = 1 := by
  simp [coprimalityDensity]

/-- **Asymptotic count of tuples coprime along the edges of a graph.** Let $k \ge 2$ and let $E$
be a set of pairs $(i, j)$ with $0 \le i < j < k$, the edge set of a graph $G$ on the vertices
$0, \dots, k-1$. Let $d_G$ be the maximum degree of $G$, that is, the largest number of pairs in
$E$ that contain a single vertex; let $\delta_G$ be the coprimality indicator and $A_G$ the
coprimality density of $G$. Then there is a real constant $C$ such that for every integer
$N \ge 2$,
$$\Bigl|\sum_{n \in \{1, \dots, N\}^k} \delta_G(n) - A_G N^k\Bigr| \le C N^{k-1} (\log N)^{d_G}.$$

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1 (`jis-2024-24.8.5-thm-1`). -/
public theorem_wanted coprimality_graph_count_asymp {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |(∑ n ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 N),
          (coprimalityIndicator E n : ℝ)) - coprimalityDensity E * (N : ℝ) ^ k|
        ≤ C * (N : ℝ) ^ (k - 1) *
          Real.log N ^ (univ.sup fun i : Fin k => (E.filter fun e => e.1 = i ∨ e.2 = i).card)

/-- **Hu's independent-set formula for the coprimality density.** Let $k$ be a natural number, let
$E$ be a set of pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$
with edge set $E$, and let $A_G$ be its coprimality density. For $0 \le m \le k$, let $i_m(G)$ be
the number of independent sets of $G$ of size $m$, that is, of sets $S \subseteq \{1, \dots, k\}$
with $|S| = m$ such that no edge of $E$ has both endpoints in $S$. Then
$$A_G = \prod_p \sum_{m=0}^{k} \frac{i_m(G)}{p^m} \left(1 - \frac{1}{p}\right)^{k-m},$$
the product running over all primes $p$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1 (`jis-2024-24.8.5-thm-1`). -/
public theorem_wanted coprimalityDensity_eq_independent_set_product {k : ℕ}
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2) :
    coprimalityDensity E =
      ∏' p : Nat.Primes, ∑ m ∈ range (k + 1),
        ((univ.filter fun S : Finset (Fin k) =>
            S.card = m ∧ ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)).card : ℝ) /
          ((p : ℕ) : ℝ) ^ m * (1 - 1 / ((p : ℕ) : ℝ)) ^ (k - m)

/-- **Multiplicativity of the coprimality indicator.** Let $G$ be a graph on the vertices
$0, \dots, k-1$ given by an arbitrary set $E$ of ordered pairs of vertices, with coprimality
indicator $\delta_G$. If $m, n \in \mathbb{N}^k$ satisfy
$\gcd(m_0 m_1 \cdots m_{k-1}, n_0 n_1 \cdots n_{k-1}) = 1$, then
$\delta_G(m_0 n_0, \dots, m_{k-1} n_{k-1}) = \delta_G(m)\, \delta_G(n)$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Lemma 4 (`jis-2024-24.8.5-lem-4`). -/
public theorem_wanted coprimalityIndicator_mul {k : ℕ} (E : Finset (Fin k × Fin k))
    (m n : Fin k → ℕ)
    (hmn : Nat.Coprime (∏ i, m i) (∏ i, n i)) :
    coprimalityIndicator E (fun i => m i * n i) =
      coprimalityIndicator E m * coprimalityIndicator E n

/-- **Inclusion–exclusion for tuples with exactly $r$ coprime pairs.** Let $k \ge 2$, $r \ge 0$
and $n \in \mathbb{N}^k$, and let $\beta_r(n)$ be $1$ if $n$ has exactly $r$ coprime pairs and $0$
otherwise. For a set $E$ of pairs $(a, b)$ with $0 \le a < b < k$, let $\delta_E$ be the
coprimality indicator of the graph with edge set $E$. Then, as integers,
$$\beta_r(n) = \sum_{j=r}^{k(k-1)/2} (-1)^{j-r} \binom{j}{r} \sum_{|E| = j} \delta_E(n),$$
where the inner sum runs over the $j$-element sets $E$ of such pairs.

For $r = 0$ this is the paper's identity for $\beta = \beta_0$, the indicator of pairwise
non-coprime tuples.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Lemma 5 (`jis-2024-24.8.5-lem-5`). -/
public theorem_wanted exactly_coprime_pairs_inclusion_exclusion {k : ℕ} (hk : 2 ≤ k)
    (r : ℕ) (n : Fin k → ℕ) :
    (if coprimePairCount n = r then 1 else 0 : ℤ) =
      ∑ j ∈ Icc r (k * (k - 1) / 2), (-1 : ℤ) ^ (j - r) * (j.choose r : ℤ) *
        ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
          (coprimalityIndicator E n : ℤ)

/-- **Inclusion–exclusion for at least $r$ coprime pairs.** Let $k \ge 2$ and $r \ge 1$, and let
$n = (n_1, \dots, n_k)$ be a tuple of natural numbers (zero allowed). Let $\beta'_r(n)$ be $1$ if
$\gcd(n_a, n_b) = 1$ for at least $r$ pairs $a < b$, and $0$ otherwise. For a set $E$ of pairs
$(a, b)$ with $1 \le a < b \le k$, let $\delta_E(n)$ be $1$ if $\gcd(n_a, n_b) = 1$ for every
$(a, b) \in E$, and $0$ otherwise. Then
$$\beta'_r(n) = \sum_{j=r}^{k(k-1)/2} (-1)^{j-r} \binom{j-1}{r-1} \sum_{|E| = j} \delta_E(n),$$
where the inner sum runs over all sets $E$ of exactly $j$ such pairs.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Lemma 6 (`jis-2024-24.8.5-lem-6`). -/
public theorem_wanted at_least_coprime_pairs_inclusion_exclusion {k : ℕ} (hk : 2 ≤ k)
    (r : ℕ) (hr : 1 ≤ r) (n : Fin k → ℕ) :
    (if r ≤ coprimePairCount n then 1 else 0 : ℤ) =
      ∑ j ∈ Icc r (k * (k - 1) / 2), (-1 : ℤ) ^ (j - r) * ((j - 1).choose (r - 1) : ℤ) *
        ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
          (coprimalityIndicator E n : ℤ)

/-- **Dirichlet series of the coprimality indicator.** Let $k \ge 2$, let $E$ be a set of pairs
$(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set $E$, and
let $J$ be a vertex cover of $G$, that is, every edge of $E$ has an endpoint in $J$. Let
$\delta_G(n_1, \dots, n_k)$ be $1$ if $\gcd(n_a, n_b) = 1$ for every $(a, b) \in E$, and $0$
otherwise. For $L \subseteq J$ let $N(L)$ be the set of vertices adjacent to some vertex of $L$.
Then for all complex numbers $s_1, \dots, s_k$ with $\operatorname{Re} s_i > 1$ for every $i$,
$$\sum_{n_1, \dots, n_k \ge 1} \frac{\delta_G(n_1, \dots, n_k)}{n_1^{s_1} \cdots n_k^{s_k}} =
\zeta(s_1) \cdots \zeta(s_k) \prod_p \sum_{L} \prod_{\ell \in L} p^{-s_\ell}
\prod_{i \in (J \setminus L) \cup (N(L) \setminus J)} \left(1 - p^{-s_i}\right),$$
where $\zeta$ is the Riemann zeta function, the product runs over all primes $p$, and the sum over
all independent sets $L \subseteq J$ of $G$, that is, subsets of $J$ such that no edge of $E$ has
both endpoints in $L$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 7 (`jis-2024-24.8.5-thm-7`). -/
public theorem_wanted coprimality_dirichlet_series_eq {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2)
    (J : Finset (Fin k)) (hJ : ∀ e ∈ E, e.1 ∈ J ∨ e.2 ∈ J)
    (s : Fin k → ℂ) (hs : ∀ i, 1 < (s i).re) :
    ∑' n : Fin k → ℕ, (coprimalityIndicator E (fun i => n i + 1) : ℂ) /
        ∏ i, ((n i + 1 : ℕ) : ℂ) ^ s i =
      (∏ i, riemannZeta (s i)) *
        ∏' p : Nat.Primes, ∑ L ∈ J.powerset.filter (fun L => ∀ e ∈ E, ¬ (e.1 ∈ L ∧ e.2 ∈ L)),
          (∏ l ∈ L, ((p : ℕ) : ℂ) ^ (-s l)) *
            ∏ i ∈ (J \ L) ∪ ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J),
              (1 - ((p : ℕ) : ℂ) ^ (-s i))

/-- **Absolute convergence of the vertex-cover Euler product.** Let $k \ge 2$, let $E$ be a set of
pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set
$E$, and let $J$ be a vertex cover of $G$, that is, every edge of $E$ has an endpoint in $J$. For
$L \subseteq J$ let $N(L)$ be the set of vertices adjacent to some vertex of $L$. For complex
numbers $s = (s_1, \dots, s_k)$ and a prime $p$ put
$$D'_{G,p}(s) = \sum_{L} \prod_{\ell \in L} p^{-s_\ell}
\prod_{i \in (J \setminus L) \cup (N(L) \setminus J)} \left(1 - p^{-s_i}\right),$$
the sum running over all independent sets $L \subseteq J$ of $G$, that is, subsets of $J$ such that
no edge of $E$ has both endpoints in $L$. Suppose that $\operatorname{Re} \sum_{i \in T} s_i > 1$
for every set $T$ of at least two vertices each of which lies on some edge of $E$. Then
$\sum_p |D'_{G,p}(s) - 1| < \infty$, the sum running over all primes $p$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 7 (`jis-2024-24.8.5-thm-7`). -/
public theorem_wanted coprimality_euler_factor_summable {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2)
    (J : Finset (Fin k)) (hJ : ∀ e ∈ E, e.1 ∈ J ∨ e.2 ∈ J) (s : Fin k → ℂ)
    (hs : ∀ T : Finset (Fin k), (∀ i ∈ T, ∃ e ∈ E, e.1 = i ∨ e.2 = i) → 2 ≤ T.card →
      1 < (∑ i ∈ T, s i).re) :
    Summable fun p : Nat.Primes =>
      ‖(∑ L ∈ J.powerset.filter (fun L => ∀ e ∈ E, ¬ (e.1 ∈ L ∧ e.2 ∈ L)),
          (∏ l ∈ L, ((p : ℕ) : ℂ) ^ (-s l)) *
            ∏ i ∈ (J \ L) ∪ ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J),
              (1 - ((p : ℕ) : ℂ) ^ (-s i))) - 1‖

/-- **Möbius-convolution series for the coprimality density.** Let $k \ge 2$, let $E$ be a set of
pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set
$E$, and let $A_G$ be its coprimality density. Let $\delta_G(n_1, \dots, n_k)$ be $1$ if
$\gcd(n_a, n_b) = 1$ for every $(a, b) \in E$, and $0$ otherwise, and for a tuple
$n = (n_1, \dots, n_k)$ of positive integers let
$$(\mu * \delta_G)(n) = \sum_{d_1 \mid n_1, \dots, d_k \mid n_k}
\mu(d_1) \cdots \mu(d_k) \, \delta_G(n_1/d_1, \dots, n_k/d_k),$$
the sum running over positive divisors $d_i$ of $n_i$, where $\mu$ is the Möbius function. Then
$$A_G = \sum_{n_1, \dots, n_k \ge 1} \frac{(\mu * \delta_G)(n)}{n_1 \cdots n_k}.$$

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`). -/
public theorem_wanted coprimalityDensity_eq_tsum_moebius_conv {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2) :
    coprimalityDensity E =
      ∑' n : Fin k → ℕ,
        (∑ d ∈ Fintype.piFinset (fun i => Nat.divisors (n i + 1)),
            (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
              (coprimalityIndicator E (fun i => (n i + 1) / d i) : ℝ)) /
          ∏ i, ((n i : ℝ) + 1)

/-- **Prime-power Euler product for the coprimality density.** Let $k \ge 2$, let $E$ be a set of
pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set
$E$, and let $A_G$ be its coprimality density. For natural numbers $n_1, \dots, n_k$ let
$\delta_G(n_1, \dots, n_k)$ be $1$ if $\gcd(n_a, n_b) = 1$ for every $(a, b) \in E$, and $0$
otherwise. Then
$$A_G = \prod_p \left(1 - \frac{1}{p}\right)^k \sum_{\nu \in \mathbb{N}^k}
\frac{\delta_G(p^{\nu_1}, \dots, p^{\nu_k})}{p^{\nu_1 + \dots + \nu_k}},$$
the product running over all primes $p$ and the sum over all $k$-tuples $\nu$ of natural numbers
(zero allowed).

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`). -/
public theorem_wanted coprimalityDensity_eq_prime_power_product {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2) :
    coprimalityDensity E =
      ∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ)) ^ k *
        ∑' ν : Fin k → ℕ, (coprimalityIndicator E (fun i => (p : ℕ) ^ ν i) : ℝ) /
          ((p : ℕ) : ℝ) ^ (∑ i, ν i)

/-- **Vertex-cover Euler product for the coprimality density.** Let $k \ge 2$, let $E$ be a set of
pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set
$E$, and let $A_G$ be its coprimality density. Let $J \subseteq \{1, \dots, k\}$ be a vertex cover
of $G$, that is, every edge of $E$ has an endpoint in $J$. For $L \subseteq J$ let $N(L)$ be the
set of vertices adjacent to some vertex of $L$. Then
$$A_G = \prod_p \sum_{L} \left(\frac{1}{p}\right)^{|L|}
\left(1 - \frac{1}{p}\right)^{|J \setminus L| + |N(L) \setminus J|},$$
where the product runs over all primes $p$ and the sum over all independent sets $L \subseteq J$
of $G$, that is, subsets of $J$ such that no edge of $E$ has both endpoints in $L$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`). -/
public theorem_wanted coprimalityDensity_eq_vertex_cover_product {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2)
    (J : Finset (Fin k)) (hJ : ∀ e ∈ E, e.1 ∈ J ∨ e.2 ∈ J) :
    coprimalityDensity E =
      ∏' p : Nat.Primes, ∑ L ∈ J.powerset.filter (fun L => ∀ e ∈ E, ¬ (e.1 ∈ L ∧ e.2 ∈ L)),
        (1 / ((p : ℕ) : ℝ)) ^ L.card * (1 - 1 / ((p : ℕ) : ℝ)) ^
          ((J \ L).card + ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card)

/-- **Asymptotic count of tuples with exactly $r$ coprime pairs.** Let $k \ge 2$ and $r \ge 0$.
For a set $E$ of pairs $(a, b)$ with $0 \le a < b < k$, let $A_E$ be the coprimality density of
the graph with edge set $E$, and put
$$C_{k,r} = \sum_{j=r}^{k(k-1)/2} (-1)^{j-r} \binom{j}{r} \sum_{|E| = j} A_E,$$
where the inner sum runs over the $j$-element sets $E$ of such pairs. Then there is a real
constant $C$ such that for every integer $N \ge 2$ the number $T_r(N)$ of tuples
$n \in \{1, \dots, N\}^k$ with exactly $r$ coprime pairs satisfies
$$|T_r(N) - C_{k,r} N^k| \le C N^{k-1} (\log N)^{k-1}.$$

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 11 (`jis-2024-24.8.5-thm-11`). -/
public theorem_wanted exactly_coprime_pairs_count_asymp {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |((Fintype.piFinset (fun _ : Fin k => Icc 1 N)).filter
            fun n => coprimePairCount n = r).card -
          (∑ j ∈ Icc r (k * (k - 1) / 2), (-1 : ℝ) ^ (j - r) * (j.choose r : ℝ) *
            ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
              coprimalityDensity E) * (N : ℝ) ^ k|
        ≤ C * (N : ℝ) ^ (k - 1) * Real.log N ^ (k - 1)

/-- **Asymptotic count of $k$-tuples with at least $r$ coprime pairs.** Let $k \ge 2$ and
$r \ge 1$. For a set $E$ of pairs $(a, b)$ with $1 \le a < b \le k$, let $A_E$ be the coprimality
density of the graph on $\{1, \dots, k\}$ with edge set $E$, and put
$$C'_{k,r} = \sum_{j=r}^{k(k-1)/2} (-1)^{j-r} \binom{j-1}{r-1} \sum_{|E| = j} A_E,$$
where the inner sum runs over all sets $E$ of exactly $j$ such pairs. Then there is a real
constant $C$ such that for every integer $N \ge 2$, the number of tuples
$(n_1, \dots, n_k) \in \{1, \dots, N\}^k$ with $\gcd(n_a, n_b) = 1$ for at least $r$ pairs
$a < b$ differs from $C'_{k,r} N^k$ by at most $C N^{k-1} (\log N)^{k-1}$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 11 (`jis-2024-24.8.5-thm-11`). -/
public theorem_wanted at_least_coprime_pairs_count_asymp {k : ℕ} (hk : 2 ≤ k) (r : ℕ)
    (hr : 1 ≤ r) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |((Fintype.piFinset (fun _ : Fin k => Icc 1 N)).filter
            fun n => r ≤ coprimePairCount n).card -
          (∑ j ∈ Icc r (k * (k - 1) / 2), (-1 : ℝ) ^ (j - r) * ((j - 1).choose (r - 1) : ℝ) *
            ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
              coprimalityDensity E) * (N : ℝ) ^ k|
        ≤ C * (N : ℝ) ^ (k - 1) * Real.log N ^ (k - 1)

/-- **The Möbius series for pairwise non-coprime tuples equals the inclusion–exclusion sum.**
Let $k \ge 2$. For a $k$-tuple $n = (n_1, \dots, n_k)$ of positive integers let $\beta(n) = 1$
if the number of coprime pairs of $n$ is $0$, that is, if $\gcd(n_i, n_j) \ne 1$ for all
$1 \le i < j \le k$, and $\beta(n) = 0$ otherwise. Let
$(\mu * \beta)(n) = \sum_{d_1 \mid n_1, \dots, d_k \mid n_k} \mu(d_1) \cdots \mu(d_k)\,
\beta(n_1/d_1, \dots, n_k/d_k)$, where $\mu$ is the Möbius function. Then
$$
\sum_{n} \frac{(\mu * \beta)(n)}{n_1 \cdots n_k}
  = \sum_{j=0}^{k(k-1)/2} (-1)^j \sum_{|E| = j} A_E,
$$
where the left sum runs over all $k$-tuples $n$ of positive integers, the inner sum on the right
runs over all sets $E$ of $j$ pairs $(i, i')$ with $1 \le i < i' \le k$, and $A_E$ is the
coprimality density of the graph on $\{1, \dots, k\}$ with edge set $E$.

In the source the common value is the density $C_k$ of pairwise non-coprime $k$-tuples. The
asymptotic count of such tuples is the case $r = 0$ of the count of $k$-tuples with exactly $r$
coprime pairs.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Corollary 12 (`jis-2024-24.8.5-cor-12`). -/
public theorem_wanted pairwise_non_coprime_density_eq_tsum_moebius_conv {k : ℕ}
    (hk : 2 ≤ k) :
    ∑' n : Fin k → ℕ,
        (∑ d ∈ Fintype.piFinset (fun i => Nat.divisors (n i + 1)),
            (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
              (if coprimePairCount (fun i => (n i + 1) / d i) = 0 then 1 else 0)) /
          ∏ i, ((n i : ℝ) + 1) =
      ∑ j ∈ range (k * (k - 1) / 2 + 1), (-1 : ℝ) ^ j *
        ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
          coprimalityDensity E

/-- **Euler product for the mean value of a multiplicative function of several variables.**
Let $f : \mathbb{N}^k \to \mathbb{C}$ satisfy $f(a_0 b_0, \dots, a_{k-1} b_{k-1}) = f(a) f(b)$
for all $a, b \in \mathbb{N}^k$ with $\gcd(a_0 \cdots a_{k-1}, b_0 \cdots b_{k-1}) = 1$. Let $\mu$
be the Möbius function, and for $n \in \mathbb{N}^k$ with every $n_i \ge 1$ put
$(\mu * f)(n) = \sum_{d} \mu(d_0) \cdots \mu(d_{k-1}) f(n_0/d_0, \dots, n_{k-1}/d_{k-1})$, the
sum over all $d \in \mathbb{N}^k$ with each $d_i$ a positive divisor of $n_i$. For a prime $p$
and $\nu \in \mathbb{N}^k$ write $p^\nu = (p^{\nu_0}, \dots, p^{\nu_{k-1}})$ and
$|\nu| = \nu_0 + \dots + \nu_{k-1}$. Assume that the family $|(\mu * f)(p^\nu)| / p^{|\nu|}$,
indexed by the pairs of a prime $p$ and a nonzero $\nu \in \mathbb{N}^k$, is summable. Then there
is a complex number $M$ such that the averages
$$\frac{1}{x_0 \cdots x_{k-1}} \sum_{1 \le n_i \le x_i} f(n)$$
(the sum over all $n \in \mathbb{N}^k$ with $1 \le n_i \le x_i$ for every $i$) tend to $M$ as
$x \in \mathbb{N}^k$ tends to infinity in every coordinate jointly, and
$$M = \prod_p \Bigl(1 - \frac{1}{p}\Bigr)^k \sum_{\nu} \frac{f(p^\nu)}{p^{|\nu|}},$$
the product running over all primes $p$ and the sum over all $\nu \in \mathbb{N}^k$.

The averages are taken over integer $x_i$; this is equivalent to real $x_i$, since only
$\lfloor x_i \rfloor$ enters the sum and $\lfloor x_i \rfloor / x_i \to 1$. The multiplicativity
hypothesis is the source's multivariable one, weaker than coordinatewise multiplicativity.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with
Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5,
Theorem 3 (`jis-2024-24.8.5-thm-3`). -/
public theorem_wanted euler_product_mean_value_of_coprime_prod
    {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, Nat.Coprime (∏ i, a i) (∏ i, b i) →
      f (fun i => a i * b i) = f a * f b)
    (hsumm : Summable (fun q : { q : { p : ℕ // p.Prime } × (Fin k → ℕ) // q.2 ≠ 0 } =>
      ‖(∑ d ∈ Fintype.piFinset (fun i => Nat.divisors ((q.1.1 : ℕ) ^ (q.1.2 i))),
          (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) *
          f (fun i => (q.1.1 : ℕ) ^ (q.1.2 i) / d i)) /
        (((q.1.1 : ℕ) : ℂ) ^ (∑ i, q.1.2 i))‖)) :
    ∃ M : ℂ, Filter.Tendsto (fun x : Fin k → ℕ =>
      (∑ n ∈ Fintype.piFinset (fun i => Finset.Icc 1 (x i)), f n) / ∏ i, (x i : ℂ))
      Filter.atTop (nhds M) ∧
      M = ∏' (p : { p : ℕ // p.Prime }),
        ((1 - 1 / ((p : ℕ) : ℂ)) ^ k *
        (∑' (ν : Fin k → ℕ),
          f (fun i => (p : ℕ) ^ (ν i)) / (((p : ℕ) : ℂ) ^ (∑ i, ν i))))

end

end MetaMathlibExt
