/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Packing `k² + 1` squares in the unit square (Erdős Problem 106)

Erdős Problem 106: draw `n` squares inside the unit square with no common interior point, and let
`f(n)` be the maximum possible sum of their side lengths. Is `f(k² + 1) = k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.Geometry.SquarePackingSideSumErdosProblem106Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #106, https://www.erdosproblems.com/106 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006723 (`EP-106`), dataset ulamai/UnsolvedMath v1.8.0.

Squares may have any orientation: a square is the image of `[0, s]²` under a rotation by `θ`
followed by a translation, with `s > 0`. 'No common interior point' is read pairwise (pairwise
disjoint interiors) and 'inside' as contained in the closed unit square `[0, 1]²` of `ℝ × ℝ`. The
page notes that `f(k² + 1) ≥ k` is easy (`k² - 1` squares of side `1/k` and two of side `1/(2k)`),
so `f(k² + 1) = k` is the bound `f(k² + 1) ≤ k`, stated for every `k ≥ 1` (`k = 0` would ask `f(1) =
0`). Orientation matters: the page defines `g` as `f` with the additional assumption that the
squares have sides parallel to those of the unit square, and records `g(k² + 1) = k` (Baek, Koizumi
and Ueoro, arXiv:2411.07274).
-/

/-- The closed square with corner `(a, b)`, side `s` and rotation angle `θ`: the points
`(a, b) + x (cos θ, sin θ) + y (-sin θ, cos θ)` with `0 ≤ x, y ≤ s`. -/
def rotatedSquare (a b θ s : ℝ) : Set (ℝ × ℝ) :=
  {q | ∃ x ∈ Set.Icc 0 s, ∃ y ∈ Set.Icc 0 s,
    q = (a + x * Real.cos θ - y * Real.sin θ, b + x * Real.sin θ + y * Real.cos θ)}

/-- The closed unit square `[0, 1]²`. -/
def unitSquare : Set (ℝ × ℝ) :=
  Set.Icc 0 1 ×ˢ Set.Icc 0 1

/-- Erdős's conjecture `f(k² + 1) = k` in its non-trivial half `f(k² + 1) ≤ k`: for every `k ≥ 1`,
any `k² + 1` squares of positive side (in any orientation) inside the unit square with pairwise
disjoint interiors have total side length at most `k`. -/
def squarePackingConjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ a b θ s : Fin (k ^ 2 + 1) → ℝ, (∀ i, 0 < s i) →
    (∀ i, rotatedSquare (a i) (b i) (θ i) (s i) ⊆ unitSquare) →
    (∀ i j, i ≠ j → Disjoint (interior (rotatedSquare (a i) (b i) (θ i) (s i)))
      (interior (rotatedSquare (a j) (b j) (θ j) (s j)))) →
    ∑ i, s i ≤ k

/--
Resolved false: erdosproblems.com/106 records that Claude Opus 5 (prompted by Silverstein) proved
`f(17) > 4`, refuting `f(k² + 1) = k` at `k = 4`: an explicit packing of `17` squares (sixteen
axis-parallel, one tilted with `cos t = 255/257`, `sin t = 32/257`) in the unit square with pairwise
disjoint interiors and total side length `2190452873/547596200 > 4`; the site lists the problem as
disproved with a Lean proof. Source: T. F. Bloom, Erdős Problems, Problem #106,
https://www.erdosproblems.com/106 (status DISPROVED (LEAN)); resolution: erdosproblems.com/106
(status DISPROVED (LEAN)): counterexample by Claude Opus 5 (prompted by Silverstein),
github.com/Sprite143/erdos-106-counterexample, page: 'A negative answer to the original question was
provided by Claude Opus 5 (prompted by Silverstein), which proved that f(17) > 4'; the repository
gives 17 squares in the unit square with pairwise disjoint interiors, sixteen axis-parallel and one
tilted (cos t = 255/257, sin t = 32/257), with exact rational coordinates and total side length
2190452873/547596200 = 4.000124... > 4, https://github.com/Sprite143/erdos-106-counterexample.
-/
public theorem_wanted squarePackingConjecture_refuted : ¬ squarePackingConjecture

end MathlibExt.Geometry.SquarePackingSideSumErdosProblem106Wanted
