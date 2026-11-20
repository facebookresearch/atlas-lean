/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarCoverageUpgrade
import Code.FK.PeriodicPlanarCriticalNontriviality
import Code.FK.PeriodicPlanarStrictNoCoexistenceReduction








open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair





theorem dualCritical_relation_of_exponentialDecay_strictNoCoexistence
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D) {q : Real}
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hq : 1 ≤ q)
    (hdecay : SubcriticalTwoPointExponentialDecay
      P q (P.criticalPoint q))
    (hstrict : StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply dualCritical_relation_of_sharpness_strictNoCoexistence
    hpc hpcDual (zero_lt_one.trans_le hq)
  · exact P.offCriticalSharpness hq hpc
  · exact Pdual.offCriticalSharpness hq hpcDual
  · exact D.dualSubcriticalCoverage_of_exponentialDecay
      H hq hdecay
  · exact hstrict




theorem dualCritical_relation_of_bidirectionalExponentialDecay_strictNoCoexistence
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (Hdual : PolynomialConnectionShells D.swap)
    {q : Real} (hq : 1 ≤ q)
    (hdecay : SubcriticalTwoPointExponentialDecay
      P q (P.criticalPoint q))
    (hdecayDual : SubcriticalTwoPointExponentialDecay
      Pdual q (Pdual.criticalPoint q))
    (hstrict : StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  obtain ⟨hcoverage, hcoverageDual⟩ :=
    D.bidirectionalSubcriticalCoverage_of_exponentialDecay
      H Hdual hq hdecay hdecayDual
  obtain ⟨hpc, hpcDual⟩ :=
    P.criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one
      Pdual hq hcoverage hcoverageDual
  exact D.dualCritical_relation_of_exponentialDecay_strictNoCoexistence
    H hpc hpcDual hq hdecay hstrict

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar
