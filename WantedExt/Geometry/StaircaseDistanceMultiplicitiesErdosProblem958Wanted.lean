/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Point sets with distance multiplicities n - 1, …, 1 (Erdős Problem 958)

Erdős Problem 958: let `A ⊂ ℝ²` be a finite set of size `n`, and let `{d_1, …, d_k}` be the set of
distances determined by `A`. Let `f(d)` be the multiplicity of `d`, that is, the number of ordered
pairs from `A` of distance `d` apart. Is it true that `k = n - 1` and `{f(d_i)} = {n - 1, …, 1}` if
and only if `A` is a set of equidistant points on a line or a circle?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Geometry.StaircaseDistanceMultiplicitiesErdosProblem958Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #958, https://www.erdosproblems.com/958 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30007100 (`EP-958`), dataset ulamai/UnsolvedMath v1.8.0.

Multiplicities count unordered pairs (MathlibExt's `distanceMultiplicity`): `n - 1, …, 1` add up to
`C(n, 2)`, the number of unordered pairs, so 'ordered pairs' cannot be meant. Only the direction
that Clemen, Dumitrescu and Liu refute is stated (multiplicities `n - 1, …, 1` force equally spaced
points on a line or a circle); the converse direction is not formalized. Equally spaced points on a
circle are consecutive points along an arc at a fixed angular step `α ≠ 0` (`IsEquallySpacedOnArc`,
formal-conjectures' `IsEquidistantOnCircle`); the step need not close up around the circle. This is
the reading under which the circle case of the 'if and only if' holds: `n` equally spaced points on
a short arc (`(n - 1) |α| ≤ π`) determine the `n - 1` chord lengths `2 r sin (j |α| / 2)`,
`1 ≤ j < n`, with multiplicities `n - 1, …, 1`, while the vertices of a regular `n`-gon determine
only `⌊n / 2⌋ < n - 1` distances when `n ≥ 3` (an equilateral triangle determines one), so with a
closing step the circle case would never apply. As in formal-conjectures the claim is for all large
`n` (small exceptions such as `{(0, 0), (1, 0), (0, 1), (0, -1)}` exist), so its refutation asserts
counterexamples of every large size. Compared with the formal-conjectures statement
`ErdosProblems/958.lean` (equivalent; no code imported).
-/

/-- `A` consists of `|A|` equally spaced points on a line: `a, a + v, …, a + (|A| - 1) v` with
`v ≠ 0`. -/
def IsEquallySpacedOnLine (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ a v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
    (A : Set (EuclideanSpace ℝ (Fin 2))) = {x | ∃ i : ℕ, i < A.card ∧ x = a + (i : ℝ) • v}

/-- `A` consists of `|A|` equally spaced points along an arc of a circle: the points of the circle
with centre `c` and radius `r > 0` at the angles `θ + i α`, `0 ≤ i < |A|`, for some step `α ≠ 0`.
The step need not close up around the circle (see the module documentation): this is the problem's
'equidistant points on a circle'. -/
def IsEquallySpacedOnArc (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ (c : EuclideanSpace ℝ (Fin 2)) (r θ α : ℝ), 0 < r ∧ α ≠ 0 ∧
    (A : Set (EuclideanSpace ℝ (Fin 2))) = {x | ∃ i : ℕ, i < A.card ∧
      x = c + r • !₂[Real.cos (θ + i * α), Real.sin (θ + i * α)]}

/-- Erdős Problem 958 (the direction Erdős expected to fail), for all large `n`: every set `A` of
`n` points of the plane that determines exactly `n - 1` distances, with multiplicities
`n - 1, …, 1` (unordered pairs; `distanceSet`, `distanceMultiplicity`, MathlibExt), consists of
equally spaced points on a line or along an arc of a circle. -/
def staircaseMultiplicitiesForceEquallySpaced : Prop :=
  ∃ N : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
    (distanceSet A).card = A.card - 1 →
    (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (A.card - 1) →
      IsEquallySpacedOnLine A ∨ IsEquallySpacedOnArc A

/--
Resolved false: Clemen, Dumitrescu and Liu proved that for every `n` there is a set of `n` points of
the plane, not all collinear or cocircular, with distance multiplicities `n - 1, n - 2, …, 1`
(equally spaced points on a short arc of a unit circle together with its centre); such a set is not
equally spaced on a line or along an arc. Source: T. F. Bloom, Erdős Problems, Problem #958,
https://www.erdosproblems.com/958 (status DISPROVED (LEAN)); resolution: F. Clemen, A. Dumitrescu
and D. Liu, On multiplicities of interpoint distances, arXiv:2505.04283 (2025), abstract, result
(4): for every n there is a set of n points of the plane, not all collinear or cocircular, with
distance multiplicities (n - 1, n - 2, …, 1); erdosproblems.com/958: equidistant points on a short
arc of a unit circle together with its centre, https://arxiv.org/abs/2505.04283.
-/
public theorem_wanted staircaseMultiplicitiesForceEquallySpaced_refuted :
    ¬ staircaseMultiplicitiesForceEquallySpaced

end MathlibExt.Geometry.StaircaseDistanceMultiplicitiesErdosProblem958Wanted
