/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopPlusWiredCut
import Code.Onsager.SignedLoopLowTempPlusLimit





open MeasureTheory Filter Topology

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice



theorem plusWiredCutRatio_tendsto_plusState
    (d : Nat) (beta : Real) (hbeta : 0 ≤ beta)
    {u v : Site d} (huv : u ≠ v)
    (path : (hypercubicLattice d).Walk u v) :
    Tendsto
      (fun n => ons_plusWiredPathNumerator d n beta u v /
        ons_plusWiredContourDenominator d n beta)
      atTop
      (nhds (∫ config, spin config u * spin config v
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  apply (plusLowTempPathRatio_tendsto_plusState
    d beta hbeta huv path).congr'
  filter_upwards [] with n
  rw [ons_plusLowTempPathNumerator_eq_wired d n beta path,
    ons_plusLowTempContourDenominator_eq_wired d n beta]

end StatMech.Onsager
