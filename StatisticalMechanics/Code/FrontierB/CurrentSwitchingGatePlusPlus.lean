/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.CurrentSwitchingGateLimit
import Code.FrontierB.CurrentTracePlusPlusUniqueness

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open Lattice Percolation

variable {d : Nat}



theorem plusPlusCurrentSwitchingGate_tendsto_unconditional
    (beta : Real) (hbeta : 0 ≤ beta) (hd : 1 ≤ d)
    {Q : Set (ConfigSpace (Sym2 (Site d)))} (hQ : IsClopen Q)
    (x y : Site d) :
    Tendsto
      (fun k =>
        let n := infiniteCurrentBoxSubsequence d beta hbeta k
        ((plusBoxCurrentMeasure d n beta hbeta).prod
          (plusBoxCurrentMeasure d n beta hbeta) : Measure _).real
          (currentPairTraceBoxGate Q k x y)) atTop
      (nhds (((infinitePlusCurrentMeasure d beta hbeta).prod
        (infinitePlusCurrentMeasure d beta hbeta) : Measure _).real
          (currentPairTraceConnectionGate Q x y))) := by
  exact plusPlusCurrentSwitchingGate_tendsto beta hbeta
    (plusPlusSuperposedTraceLaw_uniqueness d beta hbeta hd).2.1 hQ x y

end StatMech.FrontierB
