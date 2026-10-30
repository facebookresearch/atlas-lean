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

/-- `c_{n,k}(γ)`: the number of `γ`-color compositions of `n` with exactly `k`
parts, where a part equal to `j` can take on `γ j` colors.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Compositions). -/
public def coloredCompositionCount (γ : ℕ → ℕ) (n k : ℕ) : ℕ :=
  ∑ c : Composition n with c.length = k, (c.blocks.map γ).prod

/-- With one color for every part, `c_{3,2} = 2` (the compositions `(1,2)` and
`(2,1)`).

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredCompositionCount_one_three_two :
    coloredCompositionCount (fun _ => 1) 3 2 = 2 := by
  decide +kernel

/-- `d_{n,k}(γ)`: the number of Dyck paths of semilength `n` with `k` peaks in
which the primitive block `U D^j` may be colored in `γ j` ways.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Dyck paths). -/
public def coloredDyckPathCount (γ : ℕ → ℕ) (n k : ℕ) : ℕ :=
  ∑ p : {p : DyckWord // p.semilength = n} with (dyckPeakDescents p.1.toList).length = k,
    ((dyckPeakDescents p.1.toList).map γ).prod

/-- With one color for every block, `d_{3,2} = 3` (a Narayana number).

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredDyckPathCount_one_three_two :
    coloredDyckPathCount (fun _ => 1) 3 2 = 3 := by
  decide +kernel

/-- The diagonals of the convex `(n+2)`-gon with vertices `0, …, n+1` in cyclic
order: pairs `(a, b)` with `a + 2 ≤ b ≤ n + 1`, other than the side `(0, n+1)`.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def polygonDiagonals (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 2) ×ˢ Finset.range (n + 2)).filter fun e =>
    e.1 + 2 ≤ e.2 ∧ e ≠ (0, n + 1)

/-- A set of diagonals is noncrossing when no two of them cross in the interior.

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

/-- The number of vertices of the polygon of a noncrossing dissection `D` that
lies directly under the chord `e = (a, b)` (a diagonal of `D` or the root side
`(0, n+1)`), on the side of the vertices `a, …, b`: the endpoints `a`, `b`, and
the vertices strictly between them that are not strictly under another chord
`f ≠ e` of `D` with `a ≤ f.1 < f.2 ≤ b`. Every polygon of the dissection is
directly under exactly one such chord.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def dissectionFaceSize (D : Finset (ℕ × ℕ)) (e : ℕ × ℕ) : ℕ :=
  2 + ((Finset.Ioo e.1 e.2).filter fun v =>
    ∀ f ∈ D, f ≠ e → ¬ (e.1 ≤ f.1 ∧ f.1 < v ∧ v < f.2 ∧ f.2 ≤ e.2)).card

/-- `p_{n,k}(γ)`: the number of colored partitions of the rooted convex
`(n+2)`-gon made by `k - 1` noncrossing diagonals into `k` polygons, each
`(j+2)`-gon colored in `γ j` ways. For `k = 0` the sum is empty. The polygon is a genuine
polygon only for `n ≥ 1`; at `n = 0` (a degenerate `2`-gon) the count is set to `0`, so
`γ 0` never enters.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Polygon partitions). -/
public def coloredPolygonDissectionCount (γ : ℕ → ℕ) (n k : ℕ) : ℕ :=
  if n = 0 then 0 else
  ∑ D ∈ (polygonDiagonals n).powerset with IsNoncrossingDiagonalSet D ∧ D.card + 1 = k,
    ∏ e ∈ insert (0, n + 1) D, γ (dissectionFaceSize D e - 2)

/-- With one color for every polygon, `p_{3,2} = 5`: the five single diagonals of
a pentagon.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredPolygonDissectionCount_one_three_two :
    coloredPolygonDissectionCount (fun _ => 1) 3 2 = 5 := by
  decide +kernel

/-- A hexagon cut by one diagonal into two quadrilaterals or into a triangle and a
pentagon: with `γ 1 = 2`, `γ 2 = 3`, `γ 3 = 5` and `γ j = 0` otherwise,
`p_{4,2}(γ) = 3 · 3² + 6 · 2 · 5 = 87`.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
public theorem coloredPolygonDissectionCount_hexagon_two :
    coloredPolygonDissectionCount (fun j => if j = 1 then 2 else if j = 2 then 3
      else if j = 3 then 5 else 0) 4 2 = 87 := by
  decide +kernel

/-- Hoggatt and Lind's formula, as recalled by the source:
`c_{n,k}(γ) = k!/n! · B_{n,k}(1! γ_1, 2! γ_2, …)` for `n ≥ 1`.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Proposition 1 (`jis-2024-24.5.2-prop-1`), citing Hoggatt and Lind. -/
public theorem_wanted coloredCompositionCount_eq_partialBell (γ : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) :
    (coloredCompositionCount γ n k : ℚ) =
      (k.factorial : ℚ) / n.factorial *
        partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j)

/-- Mansour and Sun's formula, as recalled by the source:
`d_{n,k}(γ) = 1/(n-k+1)! · B_{n,k}(1! γ_1, 2! γ_2, …)` for `n ≥ 1`. The exponent
`n - k + 1` is written `n + 1 - k` in `ℕ`; it truncates only for `k > n + 1`, where
(as for every `k > n`) both sides vanish because `B_{n,k} = 0`.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Proposition 2 (`jis-2024-24.5.2-prop-2`), citing Mansour and Sun. -/
public theorem_wanted coloredDyckPathCount_eq_partialBell (γ : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) :
    (coloredDyckPathCount γ n k : ℚ) =
      1 / ((n + 1 - k).factorial : ℚ) *
        partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j)

/-- Birmajer, Gil, and Weiner's formula, as recalled by the source:
`p_{n,k}(γ) = 1/(n+1) · binom(n+k, k) · k!/n! · B_{n,k}(1! γ_1, 2! γ_2, …)` for
`n ≥ 1`; `k ≥ 1` is added since a partition into `k` polygons needs `k ≥ 1`.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Proposition 3 (`jis-2024-24.5.2-prop-3`), citing Birmajer, Gil, and
Weiner. -/
public theorem_wanted coloredPolygonDissectionCount_eq_partialBell (γ : ℕ → ℕ) {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (coloredPolygonDissectionCount γ n k : ℚ) =
      1 / (n + 1 : ℚ) * ((n + k).choose k : ℚ) * ((k.factorial : ℚ) / n.factorial) *
        partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j)

/-- Compositions and Dyck paths: `binom(n, k-1) c_{n,k}(γ) = k d_{n,k}(γ)` for
`1 ≤ k ≤ n` and every coloring sequence.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Theorem 4 (`jis-2024-24.5.2-thm-4`). -/
public theorem_wanted choose_mul_coloredCompositionCount_eq (γ : ℕ → ℕ) {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    n.choose (k - 1) * coloredCompositionCount γ n k = k * coloredDyckPathCount γ n k

/-- Dyck paths and polygon partitions:
`binom(n+k, k) d_{n,k}(γ) = binom(n+1, k) p_{n,k}(γ)` for `1 ≤ k ≤ n` and every
coloring sequence.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Theorem 6 (`jis-2024-24.5.2-thm-6`). -/
public theorem_wanted choose_mul_coloredDyckPathCount_eq (γ : ℕ → ℕ) {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n + k).choose k * coloredDyckPathCount γ n k =
      (n + 1).choose k * coloredPolygonDissectionCount γ n k

/-- Polygon partitions and compositions:
`(n+1) p_{n,k}(γ) = binom(n+k, k) c_{n,k}(γ)` for `1 ≤ k ≤ n` and every coloring
sequence.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Theorem 8 (`jis-2024-24.5.2-thm-8`). -/
public theorem_wanted succ_mul_coloredPolygonDissectionCount_eq (γ : ℕ → ℕ) {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n + 1) * coloredPolygonDissectionCount γ n k =
      (n + k).choose k * coloredCompositionCount γ n k

end

end MetaMathlibExt
