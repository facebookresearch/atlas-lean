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
public import MathlibExt.Combinatorics.Enumerative.ColoredDyckPathPartialBell
public import MathlibExt.Combinatorics.Enumerative.ColoredPolygonDissectionComposition
public import MathlibExt.Combinatorics.Enumerative.ColoredPolygonDissectionPartialBell
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

end

end MetaMathlibExt
