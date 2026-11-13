/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalBarrierAssembly
import Code.FrontierD.FKQgt4SquareWiredPercolation
import Code.FK.PottsPhaseCoexistenceCapstone
import Code.FK.PottsErgodicPhaseFamily










open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.FK StatMech.BeffaraDC

noncomputable section



theorem fkQgt4CriticalFreeTheta_eq_zero_of_exactDiagonalRatePos
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    FK.fkThetaFree 2
        (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) (q := q) = 0 := by
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
  let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) <= q := by linarith
  let mu0 : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  have hhalf : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
    linarith
  have hdecay := fkQgt4CriticalFreeDiagonalTwoPoint_tendsto_zero_of_rate
    hq hhalf (fkQgt4CriticalFreeDiagonalRate_tendsto_unconditional hq)
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
        mu0.real (FK.clusterInfiniteEvent 2 (origin 2) ∩
          FK.clusterInfiniteEvent 2 x) := by
    intro x
    simpa [mu0] using FK.fkgq_freeInfiniteVolume_clusterInfinite_fkg
      hp hp1 hq1 (origin 2) x
  exact percolationProbability_eq_zero_of_twoPoint_tendsto_zero
    mu0 hfreePA hfreeTI hfreeUniq
    (fun n => fkQgt4DiagonalSite (n + 1)) hdecay



theorem fkQgt4_firstOrder_of_gapRate_le
    {q : Real} (hq : 4 < q)
    (hone : fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) :
    FK.IsFirstOrderTransition 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) := by
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
  let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  have hpos := fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_gapRate_le
    hq hone
  have hFree := fkQgt4CriticalFreeTheta_eq_zero_of_exactDiagonalRatePos hq hpos
  have hWired : 0 < FK.fkTheta 2 hp hp1 hq0 (q := q) := by
    simpa [FK.fkTheta, hp, hp1, hq0] using
      fkQgt4CriticalWired_percolation_pos_of_ratePos hq hpos
  simpa [hp, hp1, hq0] using
    (FK.order_transition_q_large_selfDual hq hFree hWired).1



theorem fkQgt4_firstOrder_of_horizontalCrossing
    {q : Real} (hq : 4 < q)
    (hcross : forall scale k : Nat,
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        1 / (2 * (1 + q)) <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (3 * (scale : Int)) 0 scale)) :
    FK.IsFirstOrderTransition 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :=
  fkQgt4_firstOrder_of_gapRate_le hq
    (fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossing
      hq hcross)



theorem fkQgt4_firstOrder_of_evenHorizontalCrossingFloor
    {q crossingFloor : Real} (hq : 4 < q)
    (hcrossingFloor : 0 < crossingFloor)
    (hcross : forall scale k : Nat,
      Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        crossingFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (3 * (scale : Int)) 0 scale)) :
    FK.IsFirstOrderTransition 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :=
  fkQgt4_firstOrder_of_gapRate_le hq
    (fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenHorizontalCrossingFloor
      hq hcrossingFloor hcross)



theorem fkQgt4_critical_potts_phases_of_gapRate_le
    (q : Nat) [NeZero q] (hq : 4 < q) (J : Real) (hJ : 0 < J)
    (hone : fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit
        (by exact_mod_cast hq : (4 : Real) < q) / 2) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q))
      (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat),
      Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q
          (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧
      (∀ b, StrictMono (phiWired b) ∧
        Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b
          (pottsSelfDualInverseTemperature q J) J)
          atTop (nhds (muWired b))) ∧
      (∀ b, muFree ≠ muWired b) ∧
      ∀ b c, b ≠ c -> muWired b ≠ muWired c := by
  let hqR : (4 : Real) < q := by exact_mod_cast hq
  have hpos := fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_gapRate_le
    hqR hone
  have htheta : 0 < FK.fkTheta 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) (q := q) := by
    simpa [FK.fkTheta] using
      fkQgt4CriticalWired_percolation_pos_of_ratePos hqR hpos
  exact FK.exists_pairwise_distinct_critical_potts_phase_family_of_selfDualTheta_pos
    q hq J hJ htheta



theorem fkQgt4_critical_potts_phases_of_horizontalCrossing
    (q : Nat) [NeZero q] (hq : 4 < q) (J : Real) (hJ : 0 < J)
    (hcross : forall scale k : Nat,
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        1 / (2 * (1 + (q : Real))) <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (3 * (scale : Int)) 0 scale)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q))
      (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat),
      Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q
          (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧
      (∀ b, StrictMono (phiWired b) ∧
        Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b
          (pottsSelfDualInverseTemperature q J) J)
          atTop (nhds (muWired b))) ∧
      (∀ b, muFree ≠ muWired b) ∧
      ∀ b c, b ≠ c -> muWired b ≠ muWired c := by
  apply fkQgt4_critical_potts_phases_of_gapRate_le q hq J hJ
  exact fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossing
    (by exact_mod_cast hq : (4 : Real) < q) hcross



theorem fkQgt4_critical_ergodic_potts_phases_of_horizontalCrossing
    (q : Nat) [NeZero q] (hq : 4 < q)
    (hcross : forall scale k : Nat,
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        1 / (2 * (1 + (q : Real))) <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (3 * (scale : Int)) 0 scale)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)),
      IsErgodicFor (pottsSpinShift (d := 2) (q := q))
          (muFree : Measure _) ∧
      (forall b, IsErgodicFor (pottsSpinShift (d := 2) (q := q))
        (muWired b : Measure _)) ∧
      (forall b, muFree ≠ muWired b) ∧
      forall b c, b ≠ c -> muWired b ≠ muWired c := by
  apply FK.exists_pairwise_distinct_ergodic_critical_potts_cluster_phase_family
    q hq
  exact fkQgt4_firstOrder_of_horizontalCrossing
    (by exact_mod_cast hq : (4 : Real) < q) hcross



theorem fkQgt4_critical_ergodic_potts_phases_of_evenHorizontalCrossingFloor
    (q : Nat) [NeZero q] (hq : 4 < q)
    {crossingFloor : Real} (hcrossingFloor : 0 < crossingFloor)
    (hcross : forall scale k : Nat,
      Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        crossingFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (3 * (scale : Int)) 0 scale)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)),
      IsErgodicFor (pottsSpinShift (d := 2) (q := q))
          (muFree : Measure _) ∧
      (forall b, IsErgodicFor (pottsSpinShift (d := 2) (q := q))
        (muWired b : Measure _)) ∧
      (forall b, muFree ≠ muWired b) ∧
      forall b c, b ≠ c -> muWired b ≠ muWired c := by
  apply FK.exists_pairwise_distinct_ergodic_critical_potts_cluster_phase_family
    q hq
  exact fkQgt4_firstOrder_of_evenHorizontalCrossingFloor
    (by exact_mod_cast hq : (4 : Real) < q)
    hcrossingFloor hcross

end

end StatMech.FrontierD
