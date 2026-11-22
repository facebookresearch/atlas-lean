/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Point sets whose four-point subsets span five distances (Erdős Problem 135)

Erdős Problem 135: let `A ⊆ ℝ²` be a set of `n` points such that any `4` of them determine at least
`5` distinct distances. Must `A` determine `≫ n²` distances?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Geometry.FourPointFiveDistancesErdosProblem135Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #135, https://www.erdosproblems.com/135 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006736 (`EP-135`), dataset ulamai/UnsolvedMath v1.8.0.

`≫ n²` is read as `≥ c n²` for some `c > 0` and all large `n` (a single point determines no
distance, so small `n` must be excluded). Points are in `EuclideanSpace ℝ (Fin 2)`, and distances
are counted by MathlibExt's `distinctDistances`. formal-conjectures has no statement.
-/

open Filter

/-- Erdős Problem 135: there is `c > 0` such that for all large `n`, every set of `n` points in
the plane in which any `4` points determine at least `5` distinct distances determines at least
`c n²` distinct distances (`distinctDistances`, the number of distances between distinct
points). -/
def fourPointsFiveDistancesQuadratic : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n →
    (∀ S ⊆ A, S.card = 4 → 5 ≤ distinctDistances S) → c * (n : ℝ) ^ 2 ≤ distinctDistances A

/--
Resolved false: Tao constructed, for every large `n`, a set of `n` points in the plane in which any
four points determine at least five distinct distances but which determines only `O(n²/√(log n))`
distances; erdosproblems.com/135 lists the problem as disproved. Source: T. F. Bloom, Erdős
Problems, Problem #135, https://www.erdosproblems.com/135 (status DISPROVED (LEAN)); resolution: T.
Tao, Planar point sets with forbidden 4-point patterns and few distinct distances, arXiv:2409.01343
(2024), abstract: for any large n there is a set of n points in the plane with O(n²/√(log n))
distinct distances in which any four points determine at least five distinct distances,
https://arxiv.org/abs/2409.01343.
-/
public theorem_wanted fourPointsFiveDistancesQuadratic_refuted : ¬ fourPointsFiveDistancesQuadratic

end MathlibExt.Geometry.FourPointFiveDistancesErdosProblem135Wanted
