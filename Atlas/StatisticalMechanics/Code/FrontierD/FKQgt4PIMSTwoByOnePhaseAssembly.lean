/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedHardTransport
import Code.FrontierD.FKRectBalancedSectorThermodynamicBridge
import Code.FrontierD.FKQgt4OneWindingPhaseAssembly
import Code.FrontierD.FKQgt4WiredGlobalOrder











open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.FK StatMech.BeffaraDC
open StatMech.RSW.Box

noncomputable section



theorem fkRectDevelopedRectangleHorizontalCrossingEvent_zero
    (R : FKRectTorus) :
    fkRectDevelopedRectangleHorizontalCrossingEvent R 0 0 0 0 0 = Set.univ := by
  ext omega
  simp only [fkRectDevelopedRectangleHorizontalCrossingEvent,
    Set.mem_preimage, mem_horizontalCrossingEvent, Set.mem_univ,
    iff_true, HorizontalCrossing]
  let z : Site 2 := 0
  let x : leftSide 0 0 0 0 :=
    ⟨z, by simp [z, leftSide, rect]⟩
  let y : rightSide 0 0 0 0 :=
    ⟨z, by simp [z, rightSide, rect]⟩
  refine ⟨x, y, ?_⟩
  simpa [x, y] using
    (connectedWithin_refl (fkRectDevelopedSquarePullback R 0 omega)
      (rect 0 0 0 0) ⟨z, by simp [z, rect]⟩)


theorem fkRectCritical_developedHorizontalCrossingMass_zero
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent R 0 0 0 0 0) = 1 := by
  rw [fkRectDevelopedRectangleHorizontalCrossingEvent_zero,
    fkRectCriticalEventMass_univ R hq]





theorem fkQgt4_evenThreeByOneCrossingFloor_of_evenTwoByOneCrossingFloor
    {q hardFloor : Real} (hq : 1 <= q)
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
              0 (2 * (scale : Int)) 0 scale)) :
    forall scale k : Nat, Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor ^ 2 / (1 + q) <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (3 * (scale : Int)) 0 scale) := by
  have hsample := hcross 2 11 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨sampleBlocks, hsampleBlocks⟩ := hsample.exists
  have hhardOne : hardFloor <= 1 := by
    calc
      hardFloor <= fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily 11 2 sampleBlocks) q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            (fkRectWindingBlockVerticalFamily 11 2 sampleBlocks) 2
            0 (2 * (2 : Int)) 0 2) := hsampleBlocks
      _ <= fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily 11 2 sampleBlocks) q Set.univ :=
        fkRectCriticalEventMass_mono _ (by linarith) (Set.subset_univ _)
      _ = 1 := fkRectCriticalEventMass_univ _ (by linarith)
  have hfloorOne : hardFloor ^ 2 / (1 + q) <= 1 := by
    rw [div_le_one (by linarith : 0 < 1 + q)]
    nlinarith [sq_nonneg (hardFloor - 1)]
  intro scale k hscaleEven hwidth
  by_cases hscale : scale = 0
  · subst scale
    filter_upwards [] with blocks
    simpa using hfloorOne.trans_eq
      (fkRectCritical_developedHorizontalCrossingMass_zero
        (fkRectWindingBlockVerticalFamily k 0 blocks)
        (by linarith : (0 : Real) < q)).symm
  · have hscalePos : 0 < scale := Nat.pos_of_ne_zero hscale
    have hheightEventually : ∀ᶠ blocks in atTop,
        3 * scale <
          (fkRectWindingBlockVerticalFamily k scale blocks).height := by
      filter_upwards [eventually_ge_atTop scale] with blocks hblocks
      simp only [fkRectWindingBlockVerticalFamily_height]
      nlinarith
    filter_upwards [hcross scale k hscalePos hscaleEven hwidth,
      hheightEventually] with blocks hblocks hheight
    obtain ⟨shift, hshift⟩ := hscaleEven
    have hscaleEven' : Even scale := ⟨shift, hshift⟩
    have hshiftInt : (scale : Int) = (shift : Int) + shift := by
      exact_mod_cast hshift
    have hright : hardFloor <=
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            (fkRectWindingBlockVerticalFamily k scale blocks) scale
            scale (3 * (scale : Int)) 0 scale) := by
      apply hblocks.trans
      have htranslate :=
        fkRectCritical_horizontalCrossingMass_le_checkerboardTranslate
          (fkRectWindingBlockVerticalFamily k scale blocks) scale
          (shift : Int) shift (by linarith : (0 : Real) < q)
          0 (2 * (scale : Int)) 0 scale
      convert htranslate using 1
      all_goals simp only [hshiftInt]
      all_goals ring_nf
    apply fkRectCritical_developedThreeByOne_horizontalMass_ge_of_even_twoByOne
      (fkRectWindingBlockVerticalFamily k scale blocks) scale
      (by omega) hscaleEven'
    · simpa only [fkRectWindingBlockVerticalFamily_width] using
        (show 3 * scale < 2 * (k + 3) by omega)
    · exact hheight
    · exact hq
    · exact hhard.le
    · exact hblocks
    · exact hright



theorem fkQgt4_firstOrder_of_evenTwoByOneCrossingFloor
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
              0 (2 * (scale : Int)) 0 scale)) :
    FK.IsFirstOrderTransition 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) := by
  apply fkQgt4_firstOrder_of_evenHorizontalCrossingFloor hq
    (crossingFloor := hardFloor ^ 2 / (1 + q))
  · positivity
  · exact fkQgt4_evenThreeByOneCrossingFloor_of_evenTwoByOneCrossingFloor
      (by linarith : (1 : Real) <= q) hhard hcross




theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenTwoByOneCrossingFloor
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
              0 (2 * (scale : Int)) 0 scale)) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  apply fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenHorizontalCrossingFloor
    hq (crossingFloor := hardFloor ^ 2 / (1 + q))
  · positivity
  · exact fkQgt4_evenThreeByOneCrossingFloor_of_evenTwoByOneCrossingFloor
      (by linarith : (1 : Real) <= q) hhard hcross



theorem fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge
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
    (hfixed : forall r : Nat, 2 <= r ->
      ((r - 1 : Nat) : Real) *
          (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
        (r : Real) * fkQgt4SixVertexGapRate q) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) :=
  ⟨fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenTwoByOneCrossingFloor
      hq hhard hcross, hfixed⟩




theorem fkQgt4_phase_conclusions_of_evenTwoByOneCrossingFloor
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
              0 (2 * (scale : Int)) 0 scale)) :
    let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2))))
          (hasInfiniteClusterEvent 2) = 1 := by
  dsimp only
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
  let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  have hfirst : FK.IsFirstOrderTransition 2 hp hp1 hq0 := by
    simpa only [hp, hp1, hq0] using
      fkQgt4_firstOrder_of_evenTwoByOneCrossingFloor hq hhard hcross
  have hneq : FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
      FK.wiredInfiniteVolume 2 hp hp1 hq0 :=
    FK.freeInfiniteVolume_ne_wiredInfiniteVolume_of_firstOrder
      2 hp hp1 hq0 hfirst
  have hpos : 0 < ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (percolationEvent 2) := by
    simpa only [FK.fkTheta, hp, hp1, hq0] using hfirst.2
  have hglobal :
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2))))
          (hasInfiniteClusterEvent 2) = 1 :=
    wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_of_percolation_pos
      (d := 2) (by norm_num) hp hp1 (by linarith : (1 : Real) ≤ q) hpos
  exact ⟨hfirst, hneq, hglobal⟩




theorem fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_winding
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
  have hphase :=
    fkQgt4_phase_conclusions_of_evenTwoByOneCrossingFloor hq hhard hcross
  exact ⟨hphase.1, hphase.2.1, hphase.2.2,
    fkQgt4CriticalFreeDiagonalRate_tendsto_gap_of_winding hq hwind,
    fkQgt4SixVertexGapRate_pos hq⟩




theorem fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_fixedCharge
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
    (hfixed : forall r : Nat, 2 <= r ->
      ((r - 1 : Nat) : Real) *
          (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
        (r : Real) * fkQgt4SixVertexGapRate q) :
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
  exact fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_winding
    hq hhard hcross
      (fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge
        hq hhard hcross hfixed)





theorem fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_windingTailLimits
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
    (windingRate normalizationRate : Nat -> Nat -> Real)
    (hwindVertical : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k m) q r) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (windingRate r k)))
    (hwindHorizontal : forall r : Nat, 2 <= r ->
      Tendsto (windingRate r) atTop
        (nhds (((r - 1 : Nat) : Real) *
          (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2))))
    (hnormalizationVertical : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (normalizationRate r k)))
    (hnormalizationHorizontal : forall r : Nat, 2 <= r ->
      Tendsto (normalizationRate r) atTop (nhds 0)) :
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
  apply fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_fixedCharge
    hq hhard hcross
  intro r hr
  exact fkQgt4_fixedCharge_bound_of_windingTail_iteratedLimits
    hq r hr (windingRate r) (normalizationRate r)
      (hwindVertical r hr) (hwindHorizontal r hr)
      (hnormalizationVertical r hr) (hnormalizationHorizontal r hr)





theorem fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_uniformDiagonalLimits
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
    (hwind : forall r : Nat, 2 <= r -> forall m : Nat -> Nat,
      (forall k, k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds (((r - 1 : Nat) : Real) *
          (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2))))
    (hnormalization : forall r : Nat, 2 <= r -> forall m : Nat -> Nat,
      (forall k, k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
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
  apply fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_fixedCharge
    hq hhard hcross
  intro r hr
  exact fkQgt4_fixedCharge_bound_of_uniformDiagonalLimits
    hq r hr (hwind r hr) (hnormalization r hr)



theorem fkQgt4_critical_potts_phases_of_evenTwoByOneCrossingFloor
    (q : Nat) [NeZero q] (hq : 4 < q) (J : Real) (hJ : 0 < J)
    {hardFloor : Real} (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale)) :
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
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
  let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  have hfirst : FK.IsFirstOrderTransition 2 hp hp1 hq0 := by
    simpa only [hp, hp1, hq0] using
      fkQgt4_firstOrder_of_evenTwoByOneCrossingFloor hqR hhard hcross
  have htheta : 0 < FK.fkTheta 2 hp hp1 hq0 (q := q) := hfirst.2
  exact FK.exists_pairwise_distinct_critical_potts_phase_family_of_selfDualTheta_pos
    q hq J hJ (by simpa only [hp, hp1, hq0] using htheta)



theorem fkQgt4_critical_ergodic_potts_phases_of_evenTwoByOneCrossingFloor
    (q : Nat) [NeZero q] (hq : 4 < q)
    {hardFloor : Real} (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale)) :
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
  exact fkQgt4_firstOrder_of_evenTwoByOneCrossingFloor
    (by exact_mod_cast hq : (4 : Real) < q) hhard hcross

end

end StatMech.FrontierD
