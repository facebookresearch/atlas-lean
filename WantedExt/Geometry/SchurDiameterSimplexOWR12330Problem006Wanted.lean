/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Schur's conjecture on simplices in diameter graphs (Oberwolfach Reports 02/2013)

Oberwolfach workshop Graph Theory (2013), J. Pach, Geometric graph theory, Conjecture 1 (Schur): for
every `n ≥ d + 1`, the maximum number of `(d - 1)`-dimensional simplices in the graph of diameters
of a set of `n` points in `ℝ^d` is `n`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Pairwise

@[expose] public section

namespace MathlibExt.Geometry.SchurDiameterSimplexOWR12330Problem006Wanted

/-!
Source: J. Pach, Geometric graph theory, in Graph Theory, Oberwolfach Reports 10 (2013), Report
02/2013, p. 86, Conjecture 1, DOI 10.4171/OWR/2013/02. UnsolvedMath record UM-30002265
(`OWR-12330-006`), dataset ulamai/UnsolvedMath v1.8.0.

The diameter graph of a finite set `S ⊆ ℝ^d` of diameter `1` joins two points at distance `1`; its
`(d - 1)`-dimensional simplices are the `d`-cliques, i.e. the `d`-element subsets of `S` whose
points are pairwise at distance `1` (`unitSimplices`). "The maximum number is `n`" is stated as
`IsGreatest` over all `n`-point sets of diameter `1` (`Metric.diam = 1`), so it contains both the
upper bound and its attainment, as in Kupavskii-Polyanskii's Conjecture 1 (`D_d(d, n) = n` for `n ≥
d + 1`). The UnsolvedMath record writes `d ≠ 3` because Schur, Perles, Martini and Kupitz had
settled `d = 3`; the statement covers every `d ≥ 1` (for `d = 1` it is immediate; `ℝ⁰` has no set of
diameter `1`).
-/

open Classical in
/-- The `(d - 1)`-dimensional simplices of the diameter graph of a finite set `S ⊆ ℝ^d` of diameter
`1`: the `d`-element subsets of `S` whose points are pairwise at distance `1` (the `d`-cliques of
the graph joining two points of `S` at distance `1`). -/
noncomputable def unitSimplices {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) :
    Finset (Finset (EuclideanSpace ℝ (Fin d))) :=
  (S.powersetCard d).filter fun T =>
    (T : Set (EuclideanSpace ℝ (Fin d))).Pairwise fun x y => dist x y = 1

/-- Schur's conjecture: for `d ≥ 1` and `n ≥ d + 1`, the maximum number of `(d - 1)`-dimensional
simplices in the diameter graph of a set of `n` points of `ℝ^d` of diameter `1` is `n`. -/
def schurDiameterSimplexMax : Prop :=
  ∀ d n : ℕ, 1 ≤ d → d + 1 ≤ n →
    IsGreatest {k : ℕ | ∃ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = n ∧
      Metric.diam (S : Set (EuclideanSpace ℝ (Fin d))) = 1 ∧ (unitSimplices S).card = k} n

/--
Resolved true: Kupavskii and Polyanskii proved Schur's conjecture in every dimension: for `n ≥ d +
1` the maximum number of `d`-cliques (equivalently `(d - 1)`-dimensional simplices) in a diameter
graph on `n` vertices in `ℝ^d` is `n`. Source: J. Pach, Geometric graph theory, in Graph Theory,
Oberwolfach Reports 10 (2013), Report 02/2013, p. 86, Conjecture 1, DOI 10.4171/OWR/2013/02;
resolution: A. B. Kupavskii and A. Polyanskii, Proof of Schur's conjecture in R^d, Combinatorica 37
(2017), DOI 10.1007/s00493-016-3340-y, arXiv:1402.3694, Theorem 5(1): Schur's conjecture holds in
R^d, where Conjecture 1 (Schur et al.) is D_d(d, n) = n for n ≥ d + 1, D_d(l, n) being the maximum
number of l-cliques in a diameter graph on n vertices in R^d, https://arxiv.org/abs/1402.3694.
-/
public theorem_wanted schurDiameterSimplexMax_holds : schurDiameterSimplexMax

end MathlibExt.Geometry.SchurDiameterSimplexOWR12330Problem006Wanted
