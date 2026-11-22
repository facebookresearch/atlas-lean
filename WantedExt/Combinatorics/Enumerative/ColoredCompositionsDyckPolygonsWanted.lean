/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.DyckPeakDescents
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

open DyckStep

/-- **Number of colored compositions.** Let $\gamma = (\gamma_1, \gamma_2, \dots)$ be a sequence
of natural numbers and let $n, k$ be natural numbers. The number $c_{n,k}(\gamma)$ of
$\gamma$-colored compositions of $n$ with $k$ parts counts the compositions of $n$ with exactly $k$
parts in which each part equal to $j$ carries one of $\gamma_j$ colors: it is the sum, over all
compositions $(a_1, \dots, a_k)$ of $n$ into $k$ positive parts, of
$\gamma_{a_1} \cdots \gamma_{a_k}$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Compositions). -/
public def coloredCompositionCount (γ : ℕ → ℕ) (n k : ℕ) : ℕ :=
  ∑ c : Composition n with c.length = k, (c.blocks.map γ).prod

/-- **Compositions of 3 into two parts.** With one color for every part ($\gamma_j = 1$ for all
$j$), the number of colored compositions of $3$ with $2$ parts is $c_{3,2}(\gamma) = 2$: the
compositions $(1,2)$ and $(2,1)$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredCompositionCount_one_three_two :
    coloredCompositionCount (fun _ => 1) 3 2 = 2 := by
  decide +kernel

/-- **Number of colored Dyck paths.** Let $\gamma = (\gamma_1, \gamma_2, \dots)$ be a sequence of
natural numbers and let $n, k$ be natural numbers. In a Dyck path, each peak $UD$ together with the
maximal run of $D$ steps starting at its $D$ forms a primitive block $UD^j$. The number
$d_{n,k}(\gamma)$ counts the Dyck paths of semilength $n$ with exactly $k$ peaks in which each
primitive block $UD^j$ carries one of $\gamma_j$ colors: it is the sum, over all Dyck paths of
semilength $n$ with $k$ peaks, of the product of $\gamma_j$ over their primitive blocks $UD^j$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Dyck paths). -/
public def coloredDyckPathCount (γ : ℕ → ℕ) (n k : ℕ) : ℕ :=
  ∑ p : {p : DyckWord // p.semilength = n} with (dyckPeakDescents p.1.toList).length = k,
    ((dyckPeakDescents p.1.toList).map γ).prod

/-- **Dyck paths of semilength 3 with two peaks.** With one color for every block ($\gamma_j = 1$
for all $j$), the number of colored Dyck paths of semilength $3$ with $2$ peaks is
$d_{3,2}(\gamma) = 3$, a Narayana number.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredDyckPathCount_one_three_two :
    coloredDyckPathCount (fun _ => 1) 3 2 = 3 := by
  decide +kernel

/-- **Diagonals of a convex polygon.** For $n \in \mathbb{N}$, label the vertices of the convex
$(n+2)$-gon $0, 1, \dots, n+1$ in cyclic order. Its diagonals are the pairs $(a, b)$ of natural
numbers with $a + 2 \le b \le n + 1$ and $(a, b) \ne (0, n+1)$; the excluded pair is the side
joining the vertices $0$ and $n+1$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def polygonDiagonals (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 2) ×ˢ Finset.range (n + 2)).filter fun e =>
    e.1 + 2 ≤ e.2 ∧ e ≠ (0, n + 1)

/-- **Noncrossing sets of diagonals.** A finite set $D$ of pairs of natural numbers is
noncrossing when there are no $(a, b) \in D$ and $(c, d) \in D$ with $a < c < b < d$. For
diagonals $(a, b)$ with $a < b$ of a convex polygon whose vertices are labelled by natural numbers
in cyclic order, this says that no two diagonals of $D$ cross in the interior of the polygon.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def IsNoncrossingDiagonalSet (D : Finset (ℕ × ℕ)) : Prop :=
  ∀ e ∈ D, ∀ f ∈ D, ¬ (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2)

/-- Noncrossing is decidable.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public instance : DecidablePred IsNoncrossingDiagonalSet := fun D => by
  unfold IsNoncrossingDiagonalSet
  infer_instance

/-- **Size of the polygon under a chord.** Let $D$ be a finite set of pairs of natural numbers
and let $e = (a, b)$ be a pair of natural numbers. The face size of $e$ in $D$ is $2$ plus the
number of natural numbers $v$ with $a < v < b$ for which there is no pair $(c, d) \in D$ other
than $e$ with $a \le c < v < d \le b$. When $D$ is a noncrossing set of diagonals of the convex
$(n+2)$-gon with vertices $0, \dots, n+1$ in cyclic order and $e$ is a diagonal in $D$ or the root
side $(0, n+1)$, this is the number of vertices of the polygon of the dissection that lies
directly under $e$, on the side of the vertices $a, \dots, b$: the endpoints $a$ and $b$ and the
vertices between them that no other chord of $D$ under $e$ cuts off. Every polygon of the
dissection lies directly under exactly one such chord.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def dissectionFaceSize (D : Finset (ℕ × ℕ)) (e : ℕ × ℕ) : ℕ :=
  2 + ((Finset.Ioo e.1 e.2).filter fun v =>
    ∀ f ∈ D, f ≠ e → ¬ (e.1 ≤ f.1 ∧ f.1 < v ∧ v < f.2 ∧ f.2 ≤ e.2)).card

/-- **Colored polygon dissection count.** Let $\gamma : \mathbb{N} \to \mathbb{N}$ and
$n, k \in \mathbb{N}$. For $n \ge 1$, label the vertices of the convex $(n+2)$-gon $0, \dots, n+1$
in cyclic order, with root side $(0, n+1)$. Then $p_{n,k}(\gamma)$ is the sum, over all sets $D$ of
$k - 1$ pairwise noncrossing diagonals of this polygon, of the product, over the root side and
the diagonals $e$ of $D$, of $\gamma(j_e)$, where $j_e + 2$ is the number of vertices of the
polygon of the dissection lying directly under $e$. Every polygon of the dissection lies directly
under exactly one of these chords, so $p_{n,k}(\gamma)$ counts the partitions of the rooted
$(n+2)$-gon into $k$ polygons by $k - 1$ noncrossing diagonals in which each $(j+2)$-gon is
colored in one of $\gamma(j)$ ways. For $k = 0$ the sum is empty, so $p_{n,0}(\gamma) = 0$.
For $n = 0$ (a degenerate $2$-gon) the count is set to $p_{0,k}(\gamma) = 0$, so $\gamma(0)$
never enters.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def coloredPolygonDissectionCount (γ : ℕ → ℕ) (n k : ℕ) : ℕ :=
  if n = 0 then 0 else
  ∑ D ∈ (polygonDiagonals n).powerset with IsNoncrossingDiagonalSet D ∧ D.card + 1 = k,
    ∏ e ∈ insert (0, n + 1) D, γ (dissectionFaceSize D e - 2)

/-- **Dissections of a pentagon into two polygons.** With one color for every polygon, that is
$\gamma(j) = 1$ for all $j$, the colored polygon dissection count satisfies $p_{3,2}(\gamma) = 5$:
a convex pentagon has five diagonals, and each one cuts it into two polygons.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredPolygonDissectionCount_one_three_two :
    coloredPolygonDissectionCount (fun _ => 1) 3 2 = 5 := by
  decide +kernel

/-- **Colored dissections of a hexagon by one diagonal.** Let $\gamma_1 = 2$, $\gamma_2 = 3$,
$\gamma_3 = 5$ and $\gamma_j = 0$ for every other $j$. The number of partitions of a rooted convex
hexagon by one diagonal into $2$ polygons in which each $(j+2)$-gon carries one of $\gamma_j$
colors is $p_{4,2}(\gamma) = 87$: three diagonals cut the hexagon into two quadrilaterals and six
cut it into a triangle and a pentagon, giving $3 \cdot 3^2 + 6 \cdot 2 \cdot 5 = 87$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredPolygonDissectionCount_hexagon_two :
    coloredPolygonDissectionCount (fun j => if j = 1 then 2 else if j = 2 then 3
      else if j = 3 then 5 else 0) 4 2 = 87 := by
  decide +kernel

/-- **Hoggatt–Lind formula for colored compositions.** Let $\gamma = (\gamma_1, \gamma_2, \dots)$
be a sequence of natural numbers and let $c_{n,k}(\gamma)$ be the number of compositions of $n$
with $k$ parts in which each part $j$ carries one of $\gamma_j$ colors. For every natural number
$n \ge 1$ and every natural number $k$, as rational numbers,
$$c_{n,k}(\gamma) = \frac{k!}{n!} B_{n,k}(1! \, \gamma_1, 2! \, \gamma_2, \dots),$$
where $B_{n,k}$ is the partial Bell polynomial.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Proposition 1 (`jis-2024-24.5.2-prop-1`), citing Hoggatt and Lind. -/
public theorem_wanted coloredCompositionCount_eq_partialBell (γ : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) :
    (coloredCompositionCount γ n k : ℚ) =
      (k.factorial : ℚ) / n.factorial *
        partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j)

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

/-- **Colored Dyck paths and colored polygon partitions.** Let
$\gamma = (\gamma_1, \gamma_2, \dots)$ be a sequence of natural numbers. Let $d_{n,k}(\gamma)$ be
the number of Dyck paths of semilength $n$ with $k$ peaks in which each block $UD^j$, formed by a
peak and the maximal run of $D$ steps starting at its $D$, carries one of $\gamma_j$ colors, and
let $p_{n,k}(\gamma)$ be the number of partitions of a rooted convex $(n+2)$-gon by $k - 1$
noncrossing diagonals into $k$ polygons in which each $(j+2)$-gon carries one of $\gamma_j$
colors. For all natural numbers $n$ and $k$ with $1 \le k \le n$,
$$\binom{n+k}{k} d_{n,k}(\gamma) = \binom{n+1}{k} p_{n,k}(\gamma).$$

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Theorem 6 (`jis-2024-24.5.2-thm-6`). -/
public theorem_wanted choose_mul_coloredDyckPathCount_eq (γ : ℕ → ℕ) {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n + k).choose k * coloredDyckPathCount γ n k =
      (n + 1).choose k * coloredPolygonDissectionCount γ n k

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
