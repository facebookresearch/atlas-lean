/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticCyclePairings

/-!
# The Demailly--Paun connected-component comparison

Demailly--Paun, math/0105176v2, Main Theorem 0.1. The Kähler cone is a
connected component of the positivity set on all positive-dimensional
irreducible analytic cycles. Positivity only on curves or equality with
the whole positivity set would be stronger and is not asserted.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticCyclePairings

open KahlerClassGeometry ManifoldDifferentialForms
open scoped Manifold ContDiff

theorem_wanted kahlerCone_connectedComponent
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [SecondCountableTopology M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [ExteriorTheory ℝ (Coordinates n) M] [FiniteDimensional ℝ (H2 n M)]
    (eta : KahlerStructure n M) :
    letI := cohomologyTopology n M
    connectedComponentIn (positiveSet n M) (eta.cohomologyClass n M) = kahlerCone n M

end MathlibExt.AlgebraicGeometry.AnalyticCyclePairings

