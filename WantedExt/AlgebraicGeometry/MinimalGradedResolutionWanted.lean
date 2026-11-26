/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.RingTheory.MinimalGradedResolution
public import MathlibExt.AlgebraicGeometry.MinimalGradedResolutionBettiEq

/-!
# Minimal graded resolutions and Betti invariance

These requests add minimality and degree shifts to the ordinary resolution
scope already implemented in the audited libraries. Betti invariance
(`betti_eq`) is proved in
`MathlibExt.AlgebraicGeometry.MinimalGradedResolutionBettiEq`.
They use actual polynomial-linear differentials and kernel/range exactness.

References:
* Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*,
  Chapter 20, https://doi.org/10.1007/978-1-4612-5350-1.
* Covered ordinary-resolution source: AxiomMath/Stacks at
  c496df0d9beea9deaeabcea8492605f9a0a2313b,
  `StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/LocalSyzygy.lean`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MinimalGradedResolutionWanted

open MathlibExt.RingTheory.MinimalGradedResolution

/-- Graded Hilbert syzygy with minimal differentials and the correct length bound. -/
theorem_wanted exists_minimalResolution {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) : Nonempty (MinimalResolution G)

end WantedExt.AlgebraicGeometry.MinimalGradedResolutionWanted
