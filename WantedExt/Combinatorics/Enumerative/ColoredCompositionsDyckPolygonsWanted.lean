/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.ColoredCompositionPartialBell
public import MathlibExt.Combinatorics.Enumerative.ColoredCompositionsDyckPolygons
public import MathlibExt.Combinatorics.Enumerative.PartialBellPolynomial

/-!
# Colored compositions, Dyck paths, and polygon partitions

Statements from Gil, Hoover, and Shearer, *Bijections Between Colored
Compositions, Dyck Paths, and Polygon Partitions*, Journal of Integer Sequences
27 (2024), Article 24.5.2. A coloring sequence is `γ : ℕ → ℕ`; only the values
`γ j` with `j ≥ 1` enter (`γ 0` is unused).

* `coloredCompositionCount γ n k` (`c_{n,k}(γ)`): compositions of `n` with `k`
  parts, part `j` taking `γ j` colors.
* `coloredDyckPathCount γ n k` (`d_{n,k}(γ)`): Dyck paths (Mathlib's `DyckWord`)
  of semilength `n` with `k` peaks, the primitive block `U D^j` formed by a peak
  and its maximal descent taking `γ j` colors.
* `coloredPolygonDissectionCount γ n k` (`p_{n,k}(γ)`): partitions of a rooted
  convex `(n+2)`-gon by `k - 1` noncrossing diagonals into `k` polygons, each
  `(j+2)`-gon taking `γ j` colors. The vertices are `0, …, n+1` in cyclic order
  and the root (base) side is `(0, n+1)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Mansour–Sun formula for colored Dyck paths.** Let $\gamma = (\gamma_1, \gamma_2, \dots)$ be
a sequence of natural numbers and let $d_{n,k}(\gamma)$ be the number of Dyck paths of semilength
$n$ with $k$ peaks in which each block $UD^j$, formed by a peak and the maximal run of $D$ steps
starting at its $D$, carries one of $\gamma_j$ colors. For every natural number $n \ge 1$ and
every natural number $k$, as rational numbers,
$$d_{n,k}(\gamma) = \frac{1}{(n+1-k)!} B_{n,k}(1! \, \gamma_1, 2! \, \gamma_2, \dots),$$
where $B_{n,k}$ is the partial Bell polynomial and $n + 1 - k$ is truncated subtraction, which is
$0$ when $k > n + 1$.

For $k \le n + 1$ the factor is $1/(n-k+1)!$; for every $k > n$ both sides vanish because
$B_{n,k} = 0$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Proposition 2 (`jis-2024-24.5.2-prop-2`), citing Mansour and Sun. -/
public theorem_wanted coloredDyckPathCount_eq_partialBell (γ : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) :
    (coloredDyckPathCount γ n k : ℚ) =
      1 / ((n + 1 - k).factorial : ℚ) *
        partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j)

/-- **Birmajer–Gil–Weiner formula for colored polygon partitions.** Let
$\gamma = (\gamma_1, \gamma_2, \dots)$ be a sequence of natural numbers and let $p_{n,k}(\gamma)$
be the number of partitions of a rooted convex $(n+2)$-gon by $k - 1$ noncrossing diagonals into
$k$ polygons in which each $(j+2)$-gon carries one of $\gamma_j$ colors. For all natural numbers
$n \ge 1$ and $k \ge 1$, as rational numbers,
$$p_{n,k}(\gamma) = \frac{1}{n+1}\binom{n+k}{k}\frac{k!}{n!}B_{n,k}(1!\gamma_1, 2!\gamma_2, \dots)$$
where $B_{n,k}$ is the partial Bell polynomial.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Proposition 3 (`jis-2024-24.5.2-prop-3`), citing Birmajer, Gil, and
Weiner. -/
public theorem_wanted coloredPolygonDissectionCount_eq_partialBell (γ : ℕ → ℕ) {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (coloredPolygonDissectionCount γ n k : ℚ) =
      1 / (n + 1 : ℚ) * ((n + k).choose k : ℚ) * ((k.factorial : ℚ) / n.factorial) *
        partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j)

/-- **Colored compositions and colored Dyck paths.** Let $\gamma = (\gamma_1, \gamma_2, \dots)$
be a sequence of natural numbers. Let $c_{n,k}(\gamma)$ be the number of compositions of $n$ with
$k$ parts in which each part $j$ carries one of $\gamma_j$ colors, and let $d_{n,k}(\gamma)$ be the
number of Dyck paths of semilength $n$ with $k$ peaks in which each block $UD^j$, formed by a peak
and the maximal run of $D$ steps starting at its $D$, carries one of $\gamma_j$ colors. For all
natural numbers $n$ and $k$ with $1 \le k \le n$,
$$\binom{n}{k-1} c_{n,k}(\gamma) = k \, d_{n,k}(\gamma).$$

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Theorem 4 (`jis-2024-24.5.2-thm-4`). -/
public theorem_wanted choose_mul_coloredCompositionCount_eq (γ : ℕ → ℕ) {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    n.choose (k - 1) * coloredCompositionCount γ n k = k * coloredDyckPathCount γ n k

/-- **Polygon partitions and colored compositions.** For every coloring sequence
$\gamma : \mathbb{N} \to \mathbb{N}$ and all natural numbers $n$ and $k$ with $1 \le k \le n$, the
colored polygon dissection count $p_{n,k}(\gamma)$ and the colored composition count
$c_{n,k}(\gamma)$ satisfy
$$(n+1)\, p_{n,k}(\gamma) = \binom{n+k}{k}\, c_{n,k}(\gamma).$$

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Theorem 8 (`jis-2024-24.5.2-thm-8`). -/
public theorem_wanted succ_mul_coloredPolygonDissectionCount_eq (γ : ℕ → ℕ) {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n + 1) * coloredPolygonDissectionCount γ n k =
      (n + k).choose k * coloredCompositionCount γ n k

end

end MetaMathlibExt
