/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticCyclePairings
public import MathlibExt.AlgebraicGeometry.AnalyticCyclePairingsPullbackTheory

/-!
# The Demailly--Paun connected-component comparison

Demailly--Paun, math/0105176v2, Main Theorem 0.1. The Kähler cone is a
connected component of the positivity set on all positive-dimensional
irreducible analytic cycles. Positivity only on curves or equality with
the whole positivity set would be stronger and is not asserted. The
smoothness of pulled-back forms, a hypothesis class in `MathlibExt`, is
proved in `MathlibExt.AlgebraicGeometry.AnalyticCyclePairingsPullbackTheory`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticCyclePairingsWanted

open MathlibExt.AlgebraicGeometry
open KahlerClassGeometry ManifoldDifferentialForms AnalyticCyclePairings
open scoped Manifold ContDiff

/-- Demailly–Păun, Main Theorem 0.1: let $M$ be a compact, Hausdorff, connected,
second-countable complex manifold modelled on $\mathbb{C}^n$ (smooth as a real manifold), on which
the exterior derivative satisfies its basic laws (`ExteriorTheory`) and whose de Rham group
$H^2(M, \mathbb{R})$ is finite-dimensional, and let $\eta$ be a Kähler form on $M$. Then, for the
usual topology of $H^2(M, \mathbb{R})$, the connected component containing the class of $\eta$ of
the numerical positivity set `positiveSet` (real $(1,1)$-classes $a$ such that
$\int_Z \alpha^{\dim Z} > 0$ for every closed representative $\alpha$ of $a$ and every resolved
irreducible analytic cycle $Z$ of positive dimension) is the Kähler cone. -/
public theorem_wanted kahlerCone_connectedComponent
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [SecondCountableTopology M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [ExteriorTheory ℝ (Coordinates n) M] [FiniteDimensional ℝ (H2 n M)]
    (eta : KahlerStructure n M) :
    letI := cohomologyTopology n M
    connectedComponentIn (positiveSet n M) (eta.cohomologyClass n M) = kahlerCone n M

end WantedExt.AlgebraicGeometry.AnalyticCyclePairingsWanted
