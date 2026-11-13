/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexCriticalCapstone
import Code.FK.PeriodicPlanarCriticalNontriviality










open Set

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC FrontierA



theorem triangular_hexagonal_critical_and_decay_of_planar_inputs
    {q : Real} (hq : 1 <= q)
    (hcoverage : DualSubcriticalCoverage
      (fun r => hexagonal.wiredPercolates r q)
      (triangular.criticalPoint q) q)
    (hcoverageDual : DualSubcriticalCoverage
      (fun r => triangular.wiredPercolates r q)
      (hexagonal.criticalPoint q) q)
    (hnoCoexistence : DualNoCoexistence
      (fun r => triangular.wiredPercolates r q)
      (fun r => hexagonal.wiredPercolates r q) q) :
    (triangularFKCriticalPolynomial q
        (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧
      hexagonalFKCriticalPolynomial q
        (fkEdgeOdds (hexagonal.criticalPoint q)) = 0) ∧
    SubcriticalTwoPointExponentialDecay
      triangular q (triangular.criticalPoint q) ∧
    SubcriticalTwoPointExponentialDecay
      hexagonal q (hexagonal.criticalPoint q) := by
  obtain ⟨hpcTri, hpcHex⟩ :=
    triangular.criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one
      hexagonal hq hcoverage hcoverageDual
  have hdual :=
    triangular.dualCritical_relation_of_bidirectionalCoverage_noCoexistence
      hexagonal hq hcoverage hcoverageDual hnoCoexistence
  exact triangular_hexagonal_critical_and_decay
    hq hpcTri hpcHex hdual.1

end StatMech.FK.PeriodicPlanar
