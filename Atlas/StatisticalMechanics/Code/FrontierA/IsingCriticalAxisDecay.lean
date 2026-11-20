/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalAxisGreenComparison
import Code.FrontierA.IsingLatticeGreenBlockDecay





open Filter MeasureTheory Set Topology

namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB



theorem criticalFreeTwoPoint_axis_tendsto_zero
    {d : Nat} (hd : 2 < d) :
    Tendsto
      (fun r => currentContinuityFreeTwoPoint d
        (IsingFK.betaC (magnetization d)) (Percolation.origin d)
        (criticalAxisSite (by omega) r))
      atTop (nhds 0) := by
  let betaC := IsingFK.betaC (magnetization d)
  let i : Fin d := ⟨0, by omega⟩
  have hbetaC : 0 < betaC := by
    dsimp [betaC]
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 <= d)]
    exact tildeBetaCIsing_pos (by omega)
  have hmajorant : Tendsto
      (fun r => (1 / betaC) * isingLatticeGreenAxisBlockAverage i r)
      atTop (nhds 0) := by
    convert (isingLatticeGreenAxisBlockAverage_tendsto_zero hd i).const_mul
      (1 / betaC) using 1 <;> simp
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with r hr
    rw [currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
      betaC hbetaC (by omega) (Percolation.origin d)
      (criticalAxisSite (by omega) r)
      (criticalAxisSite_ne_origin (by omega) hr).symm]
    exact measureReal_nonneg
  · filter_upwards [eventually_ge_atTop 1] with r hr
    simpa only [betaC, i] using
      criticalFreeTwoPoint_axis_le_latticeGreenBlock hd r hr
  · exact hmajorant

end StatMech.FrontierA
