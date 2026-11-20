/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexFKCriticalSurface
import Code.FK.TriHexCriticalCandidate
import Code.FK.TriangularSharpnessCritical
import Code.FK.HexagonalSharpnessCritical





open Set

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC FrontierA



theorem triangular_hexagonal_critical_and_decay_of_finiteWiredSweep
    {q p : Real}
    (hq : 1 ≤ q)
    (hp : p ∈ Ioo (0 : Real) 1)
    (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hcriticalDual : dualParam (triangular.criticalPoint q) q =
      hexagonal.criticalPoint q)
    (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0) :
    (p = triangular.criticalPoint q ∧
      triangularFKCriticalPolynomial q
        (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧
      hexagonalFKCriticalPolynomial q
        (fkEdgeOdds (hexagonal.criticalPoint q)) = 0) ∧
    SubcriticalTwoPointExponentialDecay
      triangular q (triangular.criticalPoint q) ∧
    SubcriticalTwoPointExponentialDecay
      hexagonal q (hexagonal.criticalPoint q) := by
  exact ⟨triangular_hexagonal_critical_of_finiteWiredSweep
      hq hp hpcTri hpcHex hcriticalDual hsurface,
    triangular_subcritical_twoPoint_exponential_decay q hq hpcTri,
    hexagonal_subcritical_twoPoint_exponential_decay q hq hpcHex⟩



theorem triangular_hexagonal_critical_and_decay
    {q : Real}
    (hq : 1 ≤ q)
    (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hcriticalDual : dualParam (triangular.criticalPoint q) q =
      hexagonal.criticalPoint q) :
    (triangularFKCriticalPolynomial q
        (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧
      hexagonalFKCriticalPolynomial q
        (fkEdgeOdds (hexagonal.criticalPoint q)) = 0) ∧
    SubcriticalTwoPointExponentialDecay
      triangular q (triangular.criticalPoint q) ∧
    SubcriticalTwoPointExponentialDecay
      hexagonal q (hexagonal.criticalPoint q) := by
  obtain ⟨p, hp, hsurface⟩ := exists_triangularFKCritical_candidate hq
  have h := triangular_hexagonal_critical_and_decay_of_finiteWiredSweep
    hq hp hpcTri hpcHex hcriticalDual hsurface
  exact ⟨⟨h.1.2.1, h.1.2.2⟩, h.2.1, h.2.2⟩

end StatMech.FK.PeriodicPlanar
