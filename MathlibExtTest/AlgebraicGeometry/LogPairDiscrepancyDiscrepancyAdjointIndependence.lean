/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.LogPairDiscrepancyDiscrepancyAdjointIndependence

/-!
# Comparing two adjoint Cartier representations

The test derives equality of discrepancies computed using two independently normalized
adjoint Cartier combinations.

References: Hartshorne, *Algebraic Geometry*, II.6; Kollár--Mori,
*Birational Geometry of Algebraic Varieties*, §2.3.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.LogPairDiscrepancyDiscrepancyAdjointIndependence

open MathlibExt.AlgebraicGeometry.LogPairs
open WantedExt.AlgebraicGeometry.LogPairDiscrepancyWanted

universe u

private theorem two_presentations (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (M : BirationalModel P)
    (D E : CartierCombination P.variety)
    (hD : D.divisor = realCast (canonicalDivisor P.canonical) + P.boundary)
    (hE : E.divisor = realCast (canonicalDivisor P.canonical) + P.boundary)
    (p : PrimePoint M.variety) :
    logDiscrepancy (M.withAdjoint D hD) p = logDiscrepancy (M.withAdjoint E hE) p := by
  exact (discrepancy_adjoint_independence k n P M D hD p).symm.trans
    (discrepancy_adjoint_independence k n P M E hE p)

end MathlibExtTest.AlgebraicGeometry.LogPairDiscrepancyDiscrepancyAdjointIndependence
