/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tori cannot collapse to an interval (AimPL nnsectcurvature Problem 2.8)

AimPL: Manifolds with non-negative sectional curvature (AIM workshop, September 2007, problem list
compiled by M. Kerin), Problem 2.8 (Problem 19 of the PDF version of the list): "Can an
`n`-dimensional torus collapse to an interval? (The answer to this question is "No", essentially
settled at the workshop.)"
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.Manifold.Riemannian.Curvature
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Topology.MetricSpace.GromovHausdorff

@[expose] public section

namespace MathlibExt.Geometry.ToriCannotCollapseToIntervalAIMTopologyProblem232Wanted

/-!
Source: AimPL, Manifolds with non-negative sectional curvature, Problem 2.8 (Kerin's 2007 PDF list,
Problem 19), https://aimpl.org/nnsectcurvature/2/. UnsolvedMath record UM-20003144
(`AIM-TOPOLOGY-0232`), dataset ulamai/UnsolvedMath v1.8.0.

Reading choices. A sequence of Riemannian metrics `g_i` on the standard smooth `n`-torus is
represented by a sequence of closed `C^∞` Riemannian `n`-manifolds `M_i` (model `𝓡 n`) each
diffeomorphic to the standard torus `ℝⁿ / ℤⁿ`; pulling the metrics back along the diffeomorphisms
identifies the two settings, and Gromov-Hausdorff distances are isometry invariant. "Diffeomorphic
to `ℝⁿ / ℤⁿ`" is `IsStandardTorus`: a surjective `C^∞` local diffeomorphism `p : ℝⁿ → M` whose
fibers are exactly the `ℤⁿ`-cosets; such a `p` descends to a bijective local diffeomorphism
`ℝⁿ / ℤⁿ → M`, a diffeomorphism, and conversely. Each `M_i` carries its Riemannian distance
(`IsRiemannianManifold`), finite since `M_i` is compact and connected, as a `MetricSpace`; the
sectional curvature bound is `SectionalCurvatureGE (𝓡 n) (M i) (-1)` (MathlibExt, Levi-Civita
connection). "Collapse to an interval" is convergence in Mathlib's Gromov-Hausdorff distance
`GromovHausdorff.ghDist` to `[0, L]` with its standard metric, with `L > 0`: rescaled flat tori
converge to a point (`L = 0`).
-/

open Bundle Manifold Filter Topology
open scoped Manifold ContDiff

/-- `M` is diffeomorphic to the standard torus `ℝⁿ / ℤⁿ`: there is a surjective `C^∞` local
diffeomorphism `p : ℝⁿ → M` with `p x = p y` exactly when `x - y ∈ ℤⁿ`. -/
def IsStandardTorus (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop :=
  ∃ p : EuclideanSpace ℝ (Fin n) → M, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p ∧
    Function.Surjective p ∧ ∀ x y, p x = p y ↔ ∃ k : Fin n → ℤ, ∀ i, x i - y i = k i

/-- Tori cannot collapse to an interval: for every `n`, every `L > 0` and every sequence of closed
`C^∞` Riemannian `n`-manifolds `M_i` diffeomorphic to the standard torus with sectional curvature
`≥ -1`, the Gromov-Hausdorff distance from `M_i` to `[0, L]` does not tend to `0`. -/
def toriCannotCollapseToInterval : Prop :=
  ∀ (n : ℕ) (L : ℝ) [Fact (0 ≤ L)], 0 < L →
  ∀ (M : ℕ → Type) [∀ i, MetricSpace (M i)] [∀ i, CompactSpace (M i)] [∀ i, Nonempty (M i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M i)] [∀ i, IsManifold (𝓡 n) ∞ (M i)]
    [∀ i, RiemannianBundle (fun x : M i ↦ TangentSpace (𝓡 n) x)]
    [∀ i, IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : M i ↦ TangentSpace (𝓡 n) x)]
    [∀ i, IsRiemannianManifold (𝓡 n) (M i)],
    (∀ i, IsStandardTorus n (M i)) →
    (∀ i, SectionalCurvatureGE (𝓡 n) (M i) (-1)) →
    ¬ Tendsto (fun i ↦ GromovHausdorff.ghDist (M i) (Set.Icc (0 : ℝ) L)) atTop (𝓝 0)

/--
Resolved true (the answer to "can an n-dimensional torus collapse to an interval?" is no): metrics
of sectional curvature `≥ -1` on the standard `n`-torus never Gromov-Hausdorff converge to an
interval `[0, L]`. Source: AimPL, Manifolds with non-negative sectional curvature, Problem 2.8
(Kerin's 2007 list, Problem 19), whose own note records the answer "No"; resolution: S. Zamora, Tori
can't collapse to an interval, Electron. Res. Arch. 29 (2021), no. 4, 2637-2644, Theorem 1.7 ('Let
g_n be a sequence of Riemannian metrics of sectional curvature ≥ -1 in the m-dimensional torus M.
Then it cannot happen that the sequence (M, g_n) converges in the Gromov-Hausdorff sense to an
interval [0, L]'; abstract: manifolds 'diffeomorphic to the standard m-dimensional torus', 'a closed
interval'), https://doi.org/10.3934/era.2021005. The case n = 2 is earlier: M. G. Katz, Torus cannot
collapse to a segment, J. Geom. 111 (2020), Paper No. 13, https://doi.org/10.1007/s00022-020-0525-8.
-/
public theorem_wanted toriCannotCollapseToInterval_holds : toriCannotCollapseToInterval

end MathlibExt.Geometry.ToriCannotCollapseToIntervalAIMTopologyProblem232Wanted
