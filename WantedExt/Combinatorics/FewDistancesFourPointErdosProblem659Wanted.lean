/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Few distinct distances with every four points spanning three (Erdős Problem 659)

Erdős Problem 659: is there a set of `n` points in `ℝ²` such that every subset of `4` points
determines at least `3` distances, yet the total number of distinct distances is `≪ n / √(log n)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Combinatorics.FewDistancesFourPointErdosProblem659Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #659, https://www.erdosproblems.com/659 (status PROVED
(LEAN)). UnsolvedMath record UM-30006973 (`EP-659`), dataset ulamai/UnsolvedMath v1.8.0.

Points lie in `EuclideanSpace ℝ (Fin 2)` (Euclidean distance). The number of distinct distances is
MathlibExt's `distinctDistances` (`MathlibExt/Geometry/Metric.lean`): the number of values `dist x
y` over pairs `x ≠ y`. "A set of `n` points with `≪ n / √(log n)` distances" is read as: one
constant `C` and, for every sufficiently large `n`, an `n`-point set with at most `C n / √(log n)`
distinct distances satisfying the four-point condition. Compared with the formal-conjectures
statement `ErdosProblems/659.lean` (equivalent; no code imported).
-/

/-- **Statement of Erdős Problem 659.** This is the statement that there is a real constant $C$
such that for every sufficiently large natural number $n$ there is a set $P$ of $n$ points of the
Euclidean plane $\mathbb{R}^2$ such that every $4$-element subset of $P$ determines at least $3$
distinct distances and $P$ determines at most $C n / \sqrt{\log n}$ distinct distances. -/
def fewDistancesWithFourPointCondition : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧
    (∀ S ⊆ P, S.card = 4 → 3 ≤ distinctDistances S) ∧
    (distinctDistances P : ℝ) ≤ C * n / Real.sqrt (Real.log n)

/--
**Erdős Problem 659: few distances with every four points spanning three.** There is a real
constant $C$ such that for every sufficiently large natural number $n$ there is a set $P$ of $n$
points of the Euclidean plane $\mathbb{R}^2$ such that every $4$-element subset of $P$ determines
at least $3$ distinct distances and $P$ determines at most $C n / \sqrt{\log n}$ distinct
distances.

A suitable truncation of the lattice $\{(a, b\sqrt{2}) : a, b \in \mathbb{Z}\}$ has
$O(n / \sqrt{\log n})$ distinct distances (Moree and Osburn) and contains none of the six
four-point configurations that determine only two distances: five of them contain a square or an
equilateral triangle (Erdős–Fishburn, Lund–Sheffer), and the pentagon configuration is excluded by
Grayzel.

Source: T. F. Bloom, Erdős Problems, Problem #659, https://www.erdosproblems.com/659 (status PROVED
(LEAN)); resolution: B. Grayzel, Solution to a Problem of Erdős Concerning Distances and Points,
arXiv:2601.09102 (2026); P. Moree and R. Osburn, Two-dimensional lattices with few distances,
Enseign. Math. (2) 52 (2006), 361-380, abstract of arXiv:2601.09102: n-point sets taken from an m ×
m box of the lattice {(x, √2 y)} determine O(n / √(log n)) distinct distances (Bernays' theorem for
u² + 2v²) and every 4 of their points determine at least 3 distances (Perucca's classification of
the six two-distance 4-point configurations); erdosproblems.com/659 records the construction
(Moree-Osburn, Lund-Sheffer) and the remaining pentagon case ruled out by Grayzel (using Gemini),
'thus giving a complete solution', https://arxiv.org/abs/2601.09102.
-/
public theorem_wanted fewDistancesWithFourPointCondition_holds : fewDistancesWithFourPointCondition

end MathlibExt.Combinatorics.FewDistancesFourPointErdosProblem659Wanted
