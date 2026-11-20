/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4DiscontinuityAssembly
import Code.FrontierD.SixVertexGapCapstone

open MeasureTheory Filter Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section




theorem fkQgt4CriticalFreeTheta_eq_zero_of_gapRate
    {q : Real} (hq : 4 < q)
    (hrate : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
      (nhds (fkQgt4SixVertexGapRate q))) :
    FK.fkThetaFree 2
        (BeffaraDC.selfDualPoint_mem_Ioo
          (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo
          (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) (q := q) = 0 := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  have hq1 : (1 : Real) <= q := by linarith
  let mu0 : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  have hdecay := fkQgt4CriticalFreeDiagonalTwoPoint_tendsto_zero_of_rate
    hq (fkQgt4SixVertexGapRate_pos hq) hrate
  have hfreeTI : forall x : Site 2,
      mu0.real (FK.clusterInfiniteEvent 2 x) =
        mu0.real (FK.clusterInfiniteEvent 2 (origin 2)) := by
    intro x
    apply clusterInfiniteEvent_real_eq_origin_of_translationInvariant mu0
    simpa [mu0] using
      (FK.fkgqt_freeIV_isTranslationInvariant (d := 2) hp hp1 hq1)
  have hfreeUniq : mu0 (atLeastTwoInfinite 2) = 0 := by
    have h := (FK.freeInfinite_canonical_uniqueness_all_parameters
      (d := 2) (by norm_num) hp hp1 hq1).2.1
    simpa [mu0] using h
  change mu0.real (percolationEvent 2) = 0
  have hfreePA : forall x : Site 2,
      mu0.real (FK.clusterInfiniteEvent 2 (origin 2)) *
          mu0.real (FK.clusterInfiniteEvent 2 x) <=
        mu0.real (Set.inter (FK.clusterInfiniteEvent 2 (origin 2))
          (FK.clusterInfiniteEvent 2 x)) := by
    intro x
    simpa [mu0] using FK.fkgq_freeInfiniteVolume_clusterInfinite_fkg
      hp hp1 hq1 (origin 2) x
  exact percolationProbability_eq_zero_of_twoPoint_tendsto_zero
    mu0 hfreePA hfreeTI hfreeUniq
    (fun n => fkQgt4DiagonalSite (n + 1)) hdecay




theorem fkQgt4_firstOrder_of_gapRate_and_wiredPercolation
    {q : Real} (hq : 4 < q)
    (hrate : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
      (nhds (fkQgt4SixVertexGapRate q)))
    (hWiredAlmostSure :
      let mu := ((FK.wiredInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo
          (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo
          (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
          Measure (ConfigSpace (Sym2 (Site 2))))
      mu (percolationEvent 2) = 1) :
    And (FK.IsFirstOrderTransition 2
        (BeffaraDC.selfDualPoint_mem_Ioo
          (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo
          (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q))
      (Ne (FK.freeInfiniteVolume 2
          (BeffaraDC.selfDualPoint_mem_Ioo
            (by linarith : (0 : Real) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo
            (by linarith : (0 : Real) < q)).2
          (by linarith : (0 : Real) < q))
        (FK.wiredInfiniteVolume 2
          (BeffaraDC.selfDualPoint_mem_Ioo
            (by linarith : (0 : Real) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo
            (by linarith : (0 : Real) < q)).2
          (by linarith : (0 : Real) < q))) := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let mu1 : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.wiredInfiniteVolume 2 hp hp1 hq0
  have hFree := fkQgt4CriticalFreeTheta_eq_zero_of_gapRate hq hrate
  have hWired : 0 < FK.fkTheta 2 hp hp1 hq0 (q := q) := by
    change 0 < mu1.real (percolationEvent 2)
    unfold Measure.real
    rw [hWiredAlmostSure]
    norm_num
  simpa [hp, hp1, hq0] using
    FK.order_transition_q_large_selfDual hq hFree hWired

end

end StatMech.FrontierD
