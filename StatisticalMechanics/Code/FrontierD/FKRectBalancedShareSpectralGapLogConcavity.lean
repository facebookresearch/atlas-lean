/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule
import Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity









open Filter MeasureTheory Topology

namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section



theorem fkRectBalancedShareSpectralGap_eq_zero_of_logConcave
    {q : Real} (hq : 4 < q) (r k : Nat)
    (hlc : SixVertexSectorPerronLogConcave
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    fkRectBalancedShareSpectralGap q r k = 0 := by
  let N := sixVertexFourWidth r (k + 1)
  let c := fkQgt4SixVertexWeight q
  have hc : 0 < c := by
    dsimp [c]
    linarith [two_lt_fkQgt4SixVertexWeight hq]
  have htop := sixVertexWidthTopEigenvalue_eq_halfFilled_of_logConcave
    N (sixVertexFourWidth_even r (k + 1)) hc hlc
  have hlambda :
      sixVertexLambda N 0 (sixVertexFourWidth_even r (k + 1))
          (Nat.zero_le _) c =
        sixVertexSectorTopEigenvalue N (N / 2)
          (Nat.div_le_self N 2) c := by
    simp [sixVertexLambda]
  unfold fkRectBalancedShareSpectralGap
  change Real.log (sixVertexWidthTopEigenvalue N c) -
      Real.log (sixVertexLambda N 0 (sixVertexFourWidth_even r (k + 1))
        (Nat.zero_le _) c) = 0
  rw [htop, hlambda]
  ring



theorem fkRectBalancedShareSpectralGap_eq_zero_of_traceLogConcave
    {q : Real} (hq : 4 < q) (r k : Nat)
    (hlc : SixVertexSectorTraceLogConcave
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    fkRectBalancedShareSpectralGap q r k = 0 := by
  apply fkRectBalancedShareSpectralGap_eq_zero_of_logConcave hq r k
  exact sixVertexSectorPerronLogConcave_of_traceLogConcave
    (sixVertexFourWidth r (k + 1))
    (by linarith [two_lt_fkQgt4SixVertexWeight hq]) hlc



theorem
    fkRectBalancedShareSpectralGap_eq_zero_of_positiveEvenTraceKeyCapacityHall
    {q : Real} (hq : 4 < q) (r k : Nat)
    (hHall : SixVertexPositiveEvenTraceKeyCapacityHall
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))) :
    fkRectBalancedShareSpectralGap q r k = 0 := by
  apply fkRectBalancedShareSpectralGap_eq_zero_of_logConcave hq r k
  exact sixVertexSectorPerronLogConcave_of_positiveEvenTraceKeyCapacityHall
    (sixVertexFourWidth r (k + 1))
    (sixVertexFourWidth_pos r (k + 1))
    (sixVertexFourWidth_even r (k + 1))
    (by linarith [two_lt_fkQgt4SixVertexWeight hq]) hHall


def SixVertexCanonicalPositiveEvenTraceKeyCapacityHall : Prop :=
  forall r k : Nat,
    SixVertexPositiveEvenTraceKeyCapacityHall
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))



theorem tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_logConcave
    {q : Real} (hq : 4 < q) (r : Nat)
    (hlc : ∀ᶠ k in atTop, SixVertexSectorPerronLogConcave
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [hlc] with k hk
  exact fkRectBalancedShareSpectralGap_eq_zero_of_logConcave hq r k hk



theorem
    tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_traceLogConcave
    {q : Real} (hq : 4 < q) (r : Nat)
    (hlc : ∀ᶠ k in atTop, SixVertexSectorTraceLogConcave
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [hlc] with k hk
  exact fkRectBalancedShareSpectralGap_eq_zero_of_traceLogConcave hq r k hk



theorem tendsto_fkRectBalancedShareSpectralGap_zero_of_keyCapacityHall
    {q : Real} (hq : 4 < q) (r : Nat)
    (hHall : SixVertexCanonicalPositiveEvenTraceKeyCapacityHall) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [] with k
  exact
    fkRectBalancedShareSpectralGap_eq_zero_of_positiveEvenTraceKeyCapacityHall
      hq r k (hHall r k)



theorem fkRectBalancedShareSpectralGap_eq_base_shift
    (q : Real) (r k : Nat) :
    fkRectBalancedShareSpectralGap q r k =
      fkRectBalancedShareSpectralGap q 0 (k + r) := by
  simp [fkRectBalancedShareSpectralGap, sixVertexFourWidth,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]



theorem tendsto_fkRectBalancedShareSpectralGap_zero_of_base
    {q : Real}
    (hgap : Tendsto (fkRectBalancedShareSpectralGap q 0)
      atTop (nhds 0)) (r : Nat) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (hgap.comp (tendsto_add_atTop_nat r)).congr'
  filter_upwards [] with k
  exact (fkRectBalancedShareSpectralGap_eq_base_shift q r k).symm





structure FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity
    (q xiInv : Real) : Prop where
  winding : forall r : Nat, 2 <= r -> forall m : Nat -> Nat,
    (forall k, fkRectBoundaryIncidencePIMSHeightLower q r k <= m k) ->
    Tendsto (fun k =>
      -Real.log
          (fkRectCriticalWindingTailMass
            (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds (((r - 1 : Nat) : Real) * xiInv))
  traceLogConcavity : forall r : Nat, 2 <= r -> forall k : Nat,
    SixVertexSectorTraceLogConcave
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)



theorem
    FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity.toSpectralGap
    {q xiInv : Real} (hq : 4 < q)
    (h : FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity q xiInv) :
    FKQgt4BoundaryIncidenceScheduledSpectralGap q xiInv := by
  refine ⟨h.winding, ?_⟩
  intro r hr
  exact tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_traceLogConcave
    hq r (Filter.Eventually.of_forall fun k => h.traceLogConcavity r hr k)




theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_traceLogConcavity
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hscheduled :
      FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity q
        (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) :=
  fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap
    hq hhard hcross (hscheduled.toSpectralGap hq)




theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_traceLogConcavity_unconditional
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (htrace : forall r : Nat, 2 <= r -> forall k : Nat,
      SixVertexSectorTraceLogConcave
        (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
      hq hhard hcross
  intro r hr
  exact
    tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_traceLogConcave
      hq r (Filter.Eventually.of_forall fun k => htrace r hr k)



theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_keyCapacityHall_unconditional
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hHall : SixVertexCanonicalPositiveEvenTraceKeyCapacityHall) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
      hq hhard hcross
  intro r _hr
  exact tendsto_fkRectBalancedShareSpectralGap_zero_of_keyCapacityHall
    hq r hHall

set_option maxHeartbeats 1600000 in



theorem
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_spectralGap_unconditional
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hgap : forall r : Nat, 2 <= r ->
      Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0)) :
    let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 /\
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 /\
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) :
        Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))))
          (hasInfiniteClusterEvent 2) = 1 /\
      Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q)) /\
      0 < fkQgt4SixVertexGapRate q := by
  apply fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_winding
    hq hhard hcross
  exact
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
      hq hhard hcross hgap

set_option maxHeartbeats 1600000 in



theorem
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_baseSpectralGap
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hgap : Tendsto (fkRectBalancedShareSpectralGap q 0)
      atTop (nhds 0)) :
    let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 /\
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 /\
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) :
        Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))))
          (hasInfiniteClusterEvent 2) = 1 /\
      Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q)) /\
      0 < fkQgt4SixVertexGapRate q := by
  apply
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_spectralGap_unconditional
      hq hhard hcross
  intro r _hr
  exact tendsto_fkRectBalancedShareSpectralGap_zero_of_base hgap r

set_option maxHeartbeats 1600000 in



theorem
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_keyCapacityHall
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hHall : SixVertexCanonicalPositiveEvenTraceKeyCapacityHall) :
    let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 /\
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 /\
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) :
        Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))))
          (hasInfiniteClusterEvent 2) = 1 /\
      Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q)) /\
      0 < fkQgt4SixVertexGapRate q := by
  apply
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_spectralGap_unconditional
      hq hhard hcross
  intro r _hr
  exact tendsto_fkRectBalancedShareSpectralGap_zero_of_keyCapacityHall
    hq r hHall

end

end StatMech.FrontierD
