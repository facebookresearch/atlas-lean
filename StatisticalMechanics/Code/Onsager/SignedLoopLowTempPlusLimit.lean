/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopLowTempPlus
import Code.FrontierB.FreeBoxEvenLimit





open MeasureTheory Filter Topology BoundedContinuousFunction

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierB StatMech.Sharpness



theorem plusLowTempPathRatio_tendsto_plusState
    (d : Nat) (beta : Real) (hbeta : 0 ≤ beta)
    {u v : Site d} (huv : u ≠ v)
    (path : (hypercubicLattice d).Walk u v) :
    Tendsto
      (fun n => ons_plusLowTempPathNumerator d n beta path /
        ons_plusLowTempContourDenominator d n beta)
      atTop
      (nhds (∫ config, spin config u * spin config v
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  have hlimit := integral_plusMeasure_spinProd_full_tendsto
    d beta hbeta ({u, v} : Finset (Site d))
  have hpair : spinProd ({u, v} : Finset (Site d)) =
      (fun config => spin config u * spin config v) := by
    funext config
    rw [spinProd, Finset.prod_pair huv]
  rw [hpair] at hlimit
  apply hlimit.congr'
  filter_upwards [] with n
  exact integral_plusMeasure_twoPoint_eq_lowTempPathRatio d n beta path

end StatMech.Onsager
