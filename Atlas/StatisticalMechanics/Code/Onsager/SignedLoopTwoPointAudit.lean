/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.HighTemp
import Code.Onsager.SignedLoopCriticalWeight
import Code.Sharpness.HighTempSources
















open scoped BigOperators
open Finset

namespace StatMech.Onsager

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



noncomputable def ons_sourceX (A : Finset V) (x : Real) : Real :=
  ∑ F ∈ G.edgeFinset.powerset.filter
      (fun F => StatMech.Sharpness.HasOddBoundary F A),
    x ^ F.card



theorem ons_finiteTwoPoint_highTemp_ratio (beta : Real) {u v : V}
    (huv : u ≠ v) :
    isingExpectation G beta 0 (fun s => spin s u * spin s v) =
      ons_sourceX G {u, v} (Real.tanh beta) /
        ons_X G (Real.tanh beta) := by
  have hpair : spinProd ({u, v} : Finset V) =
      (fun s => spin s u * spin s v) := by
    funext s
    rw [spinProd, Finset.prod_pair huv]
  rw [← hpair]
  simpa [ons_sourceX, ons_X] using
    StatMech.Sharpness.expectation_spinProd_high_temp_ratio G beta {u, v}




theorem ons_finiteTwoPoint_critical_source_ratio {u v : V} (huv : u ≠ v) :
    isingExpectation G ons_betaC 0 (fun s => spin s u * spin s v) =
      ons_sourceX G {u, v} ons_signedLoopCriticalWeight /
        ons_X G ons_signedLoopCriticalWeight := by
  simpa [tanh_ons_betaC] using
    ons_finiteTwoPoint_highTemp_ratio G ons_betaC huv

end StatMech.Onsager
