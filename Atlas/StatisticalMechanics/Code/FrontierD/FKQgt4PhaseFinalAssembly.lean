/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareWiredPercolation
import Code.FrontierD.FKQgt4WiredGlobalOrder
import Code.FK.PottsPhaseCoexistenceCapstone
import Code.FK.PottsErgodicPhaseFamily

open Filter MeasureTheory Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.FK StatMech.BeffaraDC

noncomputable section




theorem fkQgt4_discontinuity_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2))))
          (hasInfiniteClusterEvent 2) = 1 ∧
      Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q)) ∧
      0 < fkQgt4SixVertexGapRate q := by
  dsimp only
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
  let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) ≤ q := by linarith
  have hpos : 0 < ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (percolationEvent 2) := by
    simpa [hp, hp1, hq0] using
      fkQgt4CriticalWired_percolation_pos_of_winding hq hwind
  have hxi : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
    linarith [fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_winding hq hwind]
  have hphase := fkQgt4_discontinuity_of_winding_and_positive_order
    hq hxi (fkQgt4CriticalFreeDiagonalRate_tendsto_unconditional hq)
      (by simpa [hp, hp1, hq0] using hpos) hwind
  have hglobal :
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2))))
          (hasInfiniteClusterEvent 2) = 1 :=
    wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_of_percolation_pos
      (d := 2) (by norm_num) hp hp1 hq1 hpos
  exact ⟨hphase.1, hphase.2.1, hglobal, hphase.2.2.1, hphase.2.2.2⟩



theorem fkQgt4_critical_potts_phases_of_winding
    (q : Nat) [NeZero q] (hq : 4 < q) (J : Real) (hJ : 0 < J)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit
        (by exact_mod_cast hq : (4 : Real) < q) / 2)
      (fkQgt4SixVertexGapRate q)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q → ProbabilityMeasure (PottsConfig 2 q))
      (phiFree : Nat → Nat) (phiWired : Fin q → Nat → Nat),
      Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q
          (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧
      (∀ b, StrictMono (phiWired b) ∧
        Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b
          (pottsSelfDualInverseTemperature q J) J)
          atTop (nhds (muWired b))) ∧
      (∀ b, muFree ≠ muWired b) ∧
      ∀ b c, b ≠ c → muWired b ≠ muWired c := by
  let hqR : (4 : Real) < q := by exact_mod_cast hq
  have htheta : 0 < FK.fkTheta 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) (q := q) := by
    simpa [FK.fkTheta] using
      fkQgt4CriticalWired_percolation_pos_of_winding hqR hwind
  exact FK.exists_pairwise_distinct_critical_potts_phase_family_of_selfDualTheta_pos
    q hq J hJ htheta



theorem fkQgt4_critical_ergodic_potts_phases_of_winding
    (q : Nat) [NeZero q] (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit
        (by exact_mod_cast hq : (4 : Real) < q) / 2)
      (fkQgt4SixVertexGapRate q)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)),
      IsErgodicFor (pottsSpinShift (d := 2) (q := q))
          (muFree : Measure _) ∧
      (forall b, IsErgodicFor (pottsSpinShift (d := 2) (q := q))
        (muWired b : Measure _)) ∧
      (forall b, muFree ≠ muWired b) ∧
      forall b c, b ≠ c -> muWired b ≠ muWired c := by
  let hqR : (4 : Real) < q := by exact_mod_cast hq
  have hphase := fkQgt4_discontinuity_of_winding hqR hwind
  exact FK.exists_pairwise_distinct_ergodic_critical_potts_cluster_phase_family
    q hq hphase.1

end

end StatMech.FrontierD
