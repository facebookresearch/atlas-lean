/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4RadialDecay
import Code.FrontierD.FKQgt4HeadlineReduction

open MeasureTheory Filter Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section



theorem fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_gapRate_le
    {q : Real} (hq : 4 < q)
    (hone : fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) :
    0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq := by
  linarith [fkQgt4SixVertexGapRate_pos hq]



theorem fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq := by
  have heq := fkQgt4_inverseCorrelation_eq_sixVertexGapRate hwind.toBounds
  have hgap := fkQgt4SixVertexGapRate_pos hq
  linarith



theorem fkQgt4CriticalFreeTwoPoint_eventually_exponential_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    exists N : Nat, forall x : Site 2, N <= fkQgt4SiteRadius x ->
      fkQgt4CriticalFreeTwoPoint hq x <=
        Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
          (fkQgt4SiteRadius x : Real)) :=
  fkQgt4CriticalFreeTwoPoint_eventually_exponential hq
    (fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_winding hq hwind)



theorem fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    exists N : Nat, forall n : Nat, N <= n ->
      ((FK.freeInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (fkQgt4CriticalFreeSphereConnectionEvent n) <=
        ((2 * n + 1 : Nat) : Real) ^ 2 *
          Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
            (n : Real)) :=
  fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential hq
    (fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_winding hq hwind)



theorem fkQgt4CriticalFreeDiagonalRate_tendsto_gap_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
      (nhds (fkQgt4SixVertexGapRate q)) := by
  have heq := fkQgt4_inverseCorrelation_eq_sixVertexGapRate hwind.toBounds
  rw [← heq]
  exact fkQgt4CriticalFreeDiagonalRate_tendsto_unconditional hq




theorem fkQgt4_firstOrder_of_winding_and_wiredPercolation
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q))
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
  exact fkQgt4_firstOrder_of_gapRate_and_wiredPercolation hq
    (fkQgt4CriticalFreeDiagonalRate_tendsto_gap_of_winding hq hwind)
    hWiredAlmostSure

end

end StatMech.FrontierD
