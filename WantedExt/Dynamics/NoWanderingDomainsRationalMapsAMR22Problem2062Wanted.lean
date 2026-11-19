/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wandering domains of rational maps (Hayman–Lingham Problem 2.62)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 2.62 (I. N. Baker): a
component `G` of the set where the iterates `fⁿ` form a normal family is a wandering domain if
`fᵏ(G) ∩ fⁿ(G) = ∅` for all `k ≠ n`, `k, n ≥ 1`. Jakobson asked whether a rational function `f` (not
of degree `0` or `1`) can have a wandering domain.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section

namespace MathlibExt.Dynamics.NoWanderingDomainsRationalMapsAMR22Problem2062Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 2.62 (I. N. Baker; question of Jakobson). UnsolvedMath
record UM-02302062 (`AMR-022-2062`), dataset ulamai/UnsolvedMath v1.8.0.

A rational map of degree at least `2` is a continuous self-map `F` of the Riemann sphere `OnePoint
ℂ` agreeing with `p/q` off the zeros of `q`, for coprime `p`, `q` with `max (deg p) (deg q) ≥ 2`;
continuity fixes the values at the poles and at `∞`. Normality of `{Fⁿ}` on an open set is stated as
equicontinuity at each of its points for the chordal distance (equivalent by Arzelà–Ascoli, the
sphere being compact); `fatouSet F` is the set of points having such a neighbourhood. A wandering
domain is a connected component of `fatouSet F` with pairwise disjoint forward images, exactly as in
the source.
-/

open OnePoint

/-- The chordal distance on the Riemann sphere `ℂ ∪ {∞}` (the unit sphere, of diameter `2`):
`2 |z - w| / (√(1 + |z|²) √(1 + |w|²))`, and `2 / √(1 + |z|²)` from `z` to `∞`. -/
noncomputable def chordalDist : OnePoint ℂ → OnePoint ℂ → ℝ
  | ∞, ∞ => 0
  | ∞, (w : ℂ) => 2 / Real.sqrt (1 + ‖w‖ ^ 2)
  | (z : ℂ), ∞ => 2 / Real.sqrt (1 + ‖z‖ ^ 2)
  | (z : ℂ), (w : ℂ) => 2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2))

/-- `F` is a rational map of degree at least `2` of the Riemann sphere: it is continuous and agrees
with `p / q` off the zeros of `q`, for coprime polynomials `p`, `q` with
`max (deg p) (deg q) ≥ 2`. -/
def IsRationalMapDegreeAtLeastTwo (F : OnePoint ℂ → OnePoint ℂ) : Prop :=
  Continuous F ∧ ∃ p q : Polynomial ℂ, IsCoprime p q ∧ 2 ≤ max p.natDegree q.natDegree ∧
    ∀ z : ℂ, q.eval z ≠ 0 → F z = ((p.eval z / q.eval z : ℂ) : OnePoint ℂ)

/-- The Fatou set of `F`: the points with a neighbourhood `U` such that the iterates `F^[n]` are
equicontinuous (for the chordal distance) at every point of `U`, i.e. form a normal family on the
interior of `U`. -/
def fatouSet (F : OnePoint ℂ → OnePoint ℂ) : Set (OnePoint ℂ) :=
  {z | ∃ U ∈ nhds z, ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ V ∈ nhds x, ∀ y ∈ V, ∀ n : ℕ,
    chordalDist (F^[n] x) (F^[n] y) < ε}

/-- Jakobson's question (Hayman–Lingham Problem 2.62): some rational map of degree at least `2`
has a wandering domain, a component `G` of its Fatou set with `F^[k] G ∩ F^[n] G = ∅` for all
`k ≠ n`, `k, n ≥ 1`. -/
def rationalMapHasWanderingDomain : Prop :=
  ∃ F : OnePoint ℂ → OnePoint ℂ, IsRationalMapDegreeAtLeastTwo F ∧ ∃ z ∈ fatouSet F,
    ∀ k n : ℕ, 1 ≤ k → 1 ≤ n → k ≠ n →
      F^[k] '' connectedComponentIn (fatouSet F) z ∩
        F^[n] '' connectedComponentIn (fatouSet F) z = ∅

/--
Resolved false: Sullivan's no-wandering-domains theorem: a rational map of degree at least `2` has
no wandering domain, so the answer to Jakobson's question is no (Hayman–Lingham Update 2.62).
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 2.62 (I. N. Baker; question of Jakobson); resolution: D.
Sullivan, Quasiconformal homeomorphisms and dynamics I. Solution of the Fatou-Julia problem on
wandering domains, Ann. of Math. 122 (1985), 401-418; recorded in Hayman–Lingham, Update 2.62,
Hayman–Lingham Update 2.62: "Sullivan has proved that rational functions have no wandering domains,
so that the answer to Jakobson's question is 'no'", https://doi.org/10.2307/1971308.
-/
public theorem_wanted rationalMapHasWanderingDomain_refuted : ¬ rationalMapHasWanderingDomain

end MathlibExt.Dynamics.NoWanderingDomainsRationalMapsAMR22Problem2062Wanted
