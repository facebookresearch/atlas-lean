/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.HodgeTateComparisonEtaleGaloisMul

/-!
# Tests for multiplication of étale Galois operators

The étale multiplication law implies the multiplication law on completed étale cohomology.

Reference: Peter Scholze, *p-adic Hodge theory for rigid-analytic varieties*,
Corollary 1.8, p. 4, and preceding Theorem 1.6 for Galois equivariance;
the algebraic scheme case follows by the comparisons described on p. 5.
https://arxiv.org/abs/1205.3463
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.HodgeTateComparisonEtaleGaloisMul

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.HodgeTateComparison

example (p : ℕ) [Fact p.Prime] (X : Over (Spec (CommRingCat.of.{0} ℚ_[p])))
    (σ τ : Galois p) (n : ℕ) :
    completedEtaleGalois p X (σ * τ) n =
      completedEtaleGalois p X σ n ∘ₗ completedEtaleGalois p X τ n :=
  completedEtaleGalois_mul p X σ τ n
    (WantedExt.AlgebraicGeometry.HodgeTateComparison.etaleGalois_mul p X σ τ n)

end MathlibExtTest.AlgebraicGeometry.HodgeTateComparisonEtaleGaloisMul
