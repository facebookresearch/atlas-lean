/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Capacity of asymmetric convex sets (Hayman–Lingham Problem 3.18)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 3.18 (E. Fraenkel):
the set `E` of least capacity `C` and given volume is a ball. If `E` displays some measure of
asymmetry (for instance, if every ball with the same volume as `E` contains a minimum proportion `δ`
in the complement of `E`), can one obtain a lower bound for the capacity of `E` which exceeds `C` by
some positive function of `δ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.FraenkelAsymmetricCapacityAMR22Problem3018Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 3.18 (E. Fraenkel). UnsolvedMath record UM-02303018
(`AMR-022-3018`), dataset ulamai/UnsolvedMath v1.8.0.

Dimension `N ≥ 3` with the Newtonian capacity `cap(E) = inf ∫ ‖∇u‖²` over smooth compactly supported
`u ≥ 1` on `E` (De Philippis–Marini–Mukoseeva, arXiv:1901.11309, (1.1)); `C = cap(B_r)` for a ball
`B_r` with the volume of `E`. The target is the theorem that the list's Update 3.18 records in the
problem's own terms: for convex sets in dimension `n ≥ 3`, `cap E ≥ C(1 + kδ^{n+1})` with `k > 0`
depending only on `n`, where every ball with the volume of `E` has at least the proportion `δ ≥ 0`
of its volume outside `E` (the problem's example of asymmetry); `E` ranges over bounded convex sets.
Not formalized: the planar case (the update's bound for general sets in the plane, stated with the
logarithmic capacity, which Mathlib lacks) and non-convex sets in dimension `N ≥ 3`, for which the
list records no answer. Fusco–Maggi–Pratelli (Ann. Sc. Norm. Super. Pisa Cl. Sci. (5) 8 (2009))
bound `cap(Ω) - cap(B_r)` below by a power of the Fraenkel asymmetry of an open set `Ω`; the list's
update does not record that result, and passing from the Fraenkel asymmetry to the problem's `δ`
would be our own step, so it is not a target.
-/

open MeasureTheory Metric
open scoped ContDiff

/-- The Newtonian capacity of `E ⊆ ℝᴺ`: the infimum of the Dirichlet energies `∫ ‖∇u‖²` of smooth
compactly supported functions `u` with `u ≥ 1` on `E`. -/
noncomputable def capacity {N : ℕ} (E : Set (EuclideanSpace ℝ (Fin N))) : ℝ :=
  sInf {c | ∃ u : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
    (∀ x ∈ E, 1 ≤ u x) ∧ c = ∫ x, ‖fderiv ℝ u x‖ ^ 2}

/-- Hall–Hayman–Weitsman's answer to Fraenkel's question for convex sets (Hayman–Lingham
Update 3.18), in dimension `N ≥ 3`: there is `k > 0` such that every bounded convex set `E` for
which every ball with the same volume as `E` has at least the proportion `δ ≥ 0` of its volume
outside `E` has capacity at least `C (1 + k δ^{N+1})`, where `C` is the capacity of a ball with
the same volume as `E`. -/
def convexAsymmetricCapacityBound : Prop :=
  ∀ N : ℕ, 3 ≤ N → ∃ k : ℝ, 0 < k ∧
    ∀ E : Set (EuclideanSpace ℝ (Fin N)), Convex ℝ E → Bornology.IsBounded E →
      ∀ r δ : ℝ, 0 ≤ δ → volume (ball (0 : EuclideanSpace ℝ (Fin N)) r) = volume E →
        (∀ x, ENNReal.ofReal δ * volume (ball x r) ≤ volume (ball x r \ E)) →
          capacity (ball (0 : EuclideanSpace ℝ (Fin N)) r) * (1 + k * δ ^ (N + 1)) ≤ capacity E

/--
Resolved true for convex sets in dimension `N ≥ 3`: Hall, Hayman and Weitsman obtain `cap E ≥ C (1 +
k δ^{N+1})`, with `k > 0` depending only on the dimension, for every convex set `E` whose
same-volume balls all have at least the proportion `δ` of their volume outside `E` (the list's
Update 3.18). Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth
Anniversary Edition (2019), arXiv:1809.07200, Problem 3.18 (E. Fraenkel); resolution: R. R. Hall, W.
K. Hayman and A. W. Weitsman, On asymmetry and capacity, J. Analyse Math. 56 (1991), 87–123, DOI
10.1007/BF02820461, as recorded in Hayman–Lingham, Update 3.18: 'Hall, Hayman and Weitsman obtain
for general sets if n = 2, and for convex sets if n ≥ 3, cap E ≥ C(1 + kδ^{n+1}), where k is a
constant depending on the dimension n', https://arxiv.org/abs/1809.07200.
-/
public theorem_wanted convexAsymmetricCapacityBound_holds : convexAsymmetricCapacityBound

end MathlibExt.Analysis.FraenkelAsymmetricCapacityAMR22Problem3018Wanted
