/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.RingTheory.MinimalGradedResolution

/-!
# Minimal graded resolutions and Betti invariance

These requests add minimality, degree shifts and Betti invariance to the
ordinary resolution scope already implemented in the audited libraries.
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

variable {k : Type*} [Field k] {n : ℕ} {M : Type*}
  [AddCommGroup M] [Module (PolynomialRing k n) M]
  [Module k M] [IsScalarTower k (PolynomialRing k n) M]
  [Module.Finite (PolynomialRing k n) M]

/-- Graded Hilbert syzygy with minimal differentials and the correct length bound. -/
theorem_wanted exists_minimalResolution
    (G : Grading (k := k) (n := n) (M := M)) : Nonempty (MinimalResolution G)

/-- The graded Betti table does not depend on the chosen minimal resolution. -/
theorem_wanted betti_eq (G : Grading (k := k) (n := n) (M := M))
    (P Q : MinimalResolution G) (i : ℕ) (j : ℤ) :
    betti G P i j = betti G Q i j

end WantedExt.AlgebraicGeometry.MinimalGradedResolutionWanted
