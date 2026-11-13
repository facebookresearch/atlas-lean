/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBalancedShareVerticalRate
import Code.FrontierD.FKRectAllSectorWidthRate
import Code.FrontierD.FKRectBoundaryIncidenceRateCapstone
import Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule
import Code.FrontierD.FKRectBoundaryIncidencePIMSPhaseAssembly







open Filter Topology MeasureTheory

namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section



theorem exists_nat_uniform_lower_tendsto_above
    (f : Nat -> Nat -> Real) (a : Nat -> Real) {L : Real}
    (prescribed : Nat -> Nat)
    (hvertical : forall k, Tendsto (f k) atTop (nhds (a k)))
    (hhorizontal : Tendsto a atTop (nhds L)) :
    exists lower : Nat -> Nat,
      (forall k, prescribed k <= lower k) /\
      forall m : Nat -> Nat, (forall k, lower k <= m k) ->
        Tendsto (fun k => f k (m k)) atTop (nhds L) := by
  have hchoose (k : Nat) : exists M : Nat, forall n : Nat, M <= n ->
      dist (f k n) (a k) < (1 : Real) / (k + 1) := by
    have heps : 0 < (1 : Real) / (k + 1) := by positivity
    have hev : ∀ᶠ n in atTop,
        f k n ∈ Metric.ball (a k) ((1 : Real) / (k + 1)) :=
      hvertical k (Metric.ball_mem_nhds _ heps)
    obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    exact ⟨M, fun n hn => by
      simpa only [Metric.mem_ball] using hM n hn⟩
  choose M hM using hchoose
  let lower : Nat -> Nat := fun k => max (prescribed k) (M k)
  refine ⟨lower, fun k => le_max_left _ _, ?_⟩
  intro m hm
  have herr (k : Nat) :
      dist (f k (m k)) (a k) <= (1 : Real) / (k + 1) := by
    exact (hM k (m k) ((le_max_right _ _).trans (hm k))).le
  have heps : Tendsto (fun k : Nat => (1 : Real) / (k + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have haDist : Tendsto (fun k => dist (a k) L) atTop (nhds 0) :=
    (tendsto_iff_dist_tendsto_zero).1 hhorizontal
  have hdist : Tendsto (fun k => dist (f k (m k)) L)
      atTop (nhds 0) := by
    apply squeeze_zero (g := fun k =>
      (1 : Real) / (k + 1) + dist (a k) L)
    · exact fun _ => dist_nonneg
    · intro k
      calc
        dist (f k (m k)) L <=
            dist (f k (m k)) (a k) + dist (a k) L :=
          dist_triangle _ _ _
        _ <= (1 : Real) / (k + 1) + dist (a k) L := by
          exact add_le_add (herr k) le_rfl
    · simpa using heps.add haDist
  exact (tendsto_iff_dist_tendsto_zero).2 hdist



noncomputable def fkRectBalancedShareSpectralGap
    (q : Real) (r k : Nat) : Real :=
  Real.log (sixVertexWidthTopEigenvalue
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) -
    Real.log (sixVertexLambda (sixVertexFourWidth r (k + 1)) 0
      (sixVertexFourWidth_even r (k + 1)) (Nat.zero_le _)
      (fkQgt4SixVertexWeight q))



theorem fkRectBalancedSectorShare_fixedCharge_vertical_negLog_tendsto
    {q : Real} (hq : 4 < q) (r k : Nat) :
    Tendsto (fun m =>
      -Real.log (fkRectBalancedSectorShare
          (fkRectFixedChargeVerticalFamily r k m) q) /
        (fkRectFixedChargeVerticalFamily r k m).height)
      atTop (nhds (fkRectBalancedShareSpectralGap q r k)) := by
  have hindex : Tendsto (fun m : Nat => 2 * (m + 2)) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 <| ⟨N, fun m hm => by omega⟩
  have h := (sixVertexBalancedTraceShare_negLog_div_height_tendsto
    (sixVertexFourWidth r (k + 1))
    (sixVertexFourWidth_even r (k + 1))
    (by linarith [two_lt_fkQgt4SixVertexWeight hq] :
      0 < fkQgt4SixVertexWeight q)).comp hindex
  apply h.congr'
  filter_upwards [] with m
  rw [fkRectFixedChargeVerticalFamily_balancedShare_eq_traceShare r k m hq]
  simp only [fkRectFixedChargeVerticalFamily_medialWidth,
    fkRectFixedChargeVerticalFamily_medialHeight,
    fkRectFixedChargeVerticalFamily_height, Function.comp_apply]




noncomputable def fkRectBalancedSectorNormalizationVerticalRate
    {q : Real} (hq : 4 < q) (r k : Nat) : Real :=
  fkRectAllSectorNormalizationVerticalRate hq r k +
    fkRectBalancedShareSpectralGap q r k



theorem fkRectBalancedSectorNormalization_vertical_negLog_tendsto_rate
    {q : Real} (hq : 4 < q) (r k : Nat) :
    Tendsto (fun m =>
      -Real.log (fkRectBalancedSectorNormalization
          (fkRectFixedChargeVerticalFamily r k m) q) /
        (fkRectFixedChargeVerticalFamily r k m).height)
      atTop
      (nhds (fkRectBalancedSectorNormalizationVerticalRate hq r k)) := by
  have hall :=
    fkRectAllSectorNormalization_vertical_negLog_tendsto_rate hq r k
  have hshare :=
    fkRectBalancedSectorShare_fixedCharge_vertical_negLog_tendsto hq r k
  have hadd := hall.add hshare
  apply hadd.congr'
  filter_upwards [] with m
  rw [balancedNormalization_negLog_eq_all_add_share
    (fkRectFixedChargeVerticalFamily r k m) hq]
  ring




theorem
    tendsto_fkRectBalancedSectorNormalizationVerticalRate_zero_of_freePIMS_and_spectralGap
    {q : Real} (hq : 4 < q) (r : Nat)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (by linarith : 0 < q))
        (fkRectCriticalP_lt_one (by linarith : 0 < q))
        (by linarith : 0 < q) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0)
    (hgap : Tendsto (fkRectBalancedShareSpectralGap q r)
      atTop (nhds 0)) :
    Tendsto (fkRectBalancedSectorNormalizationVerticalRate hq r)
      atTop (nhds 0) := by
  have hall :=
    tendsto_fkRectAllSectorNormalizationVerticalRate_zero_of_freePIMS
      hq r hperc
  simpa [fkRectBalancedSectorNormalizationVerticalRate] using
    hall.add hgap




theorem exists_fkRectBalancedNormalization_spectralHeightLower
    {q : Real} (hq : 4 < q) (r : Nat)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (by linarith : 0 < q))
        (fkRectCriticalP_lt_one (by linarith : 0 < q))
        (by linarith : 0 < q) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0)
    (hgap : Tendsto (fkRectBalancedShareSpectralGap q r)
      atTop (nhds 0)) :
    exists heightLower : Nat -> Nat,
      (forall k,
        fkRectBoundaryIncidencePIMSHeightLower q r k <= heightLower k) /\
      forall m : Nat -> Nat, (forall k, heightLower k <= m k) ->
        Tendsto (fun k =>
          -Real.log (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
            (fkRectFixedChargeVerticalFamily r k (m k)).height)
          atTop (nhds 0) := by
  exact exists_nat_uniform_lower_tendsto_above
    (fun k m =>
      -Real.log (fkRectBalancedSectorNormalization
          (fkRectFixedChargeVerticalFamily r k m) q) /
        (fkRectFixedChargeVerticalFamily r k m).height)
    (fkRectBalancedSectorNormalizationVerticalRate hq r)
    (fkRectBoundaryIncidencePIMSHeightLower q r)
    (fkRectBalancedSectorNormalization_vertical_negLog_tendsto_rate hq r)
    (tendsto_fkRectBalancedSectorNormalizationVerticalRate_zero_of_freePIMS_and_spectralGap
      hq r hperc hgap)




theorem
    fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap_unconditional
    {q : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (by linarith : 0 < q))
        (fkRectCriticalP_lt_one (by linarith : 0 < q))
        (by linarith : 0 < q) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0)
    (hgap : Tendsto (fkRectBalancedShareSpectralGap q r)
      atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) *
        (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  exact fkQgt4_fixedCharge_bound_of_normalizationLimits_unconditional
    hq r hr (fkRectBalancedSectorNormalizationVerticalRate hq r)
    (fkRectBalancedSectorNormalization_vertical_negLog_tendsto_rate hq r)
    (tendsto_fkRectBalancedSectorNormalizationVerticalRate_zero_of_freePIMS_and_spectralGap
      hq r hperc hgap)




theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
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
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge
    hq hhard hcross
  intro r hr
  apply fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap_unconditional
    hq r hr
  · exact
      fkQgt4CriticalFree_percolation_zero_of_evenTwoByOneCrossingFloor
        hq hhard hcross
  · exact hgap r hr



theorem exists_fkRectBalancedShare_spectralHeightLower
    {q : Real} (hq : 4 < q) (r : Nat)
    (hgap : Tendsto (fkRectBalancedShareSpectralGap q r)
      atTop (nhds 0)) :
    exists heightLower : Nat -> Nat,
      (forall k,
        fkRectBoundaryIncidencePIMSHeightLower q r k <= heightLower k) /\
      forall m : Nat -> Nat, (forall k, heightLower k <= m k) ->
        Tendsto (fun k =>
          -Real.log (fkRectBalancedSectorShare
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
            (fkRectFixedChargeVerticalFamily r k (m k)).height)
          atTop (nhds 0) := by
  exact exists_nat_uniform_lower_tendsto_above
    (fun k m =>
      -Real.log (fkRectBalancedSectorShare
          (fkRectFixedChargeVerticalFamily r k m) q) /
        (fkRectFixedChargeVerticalFamily r k m).height)
    (fkRectBalancedShareSpectralGap q r)
    (fkRectBoundaryIncidencePIMSHeightLower q r)
    (fkRectBalancedSectorShare_fixedCharge_vertical_negLog_tendsto hq r)
    hgap


theorem fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_balancedShare
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (heightLower : Nat -> Nat)
    (hwind : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (hnoLoop : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectAllSectorNormalization
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0))
    (hshare : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectBalancedSectorShare
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  apply fkQgt4_fixedCharge_bound_of_uniformDiagonalLimitsAbove
    hq r hr heightLower hwind
  intro m hm
  have hadd := (hnoLoop m hm).add (hshare m hm)
  have heq : (fun k =>
      -Real.log
          (fkRectBalancedSectorNormalization
            (fkRectFixedChargeVerticalFamily r k (m k)) q) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height) =
      (fun k =>
        -Real.log
            (fkRectAllSectorNormalization
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height +
        -Real.log
            (fkRectBalancedSectorShare
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height) := by
    funext k
    rw [balancedNormalization_negLog_eq_all_add_share
      (fkRectFixedChargeVerticalFamily r k (m k)) hq]
    ring
  rw [heq]
  simpa using hadd



theorem
    fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_balancedShare
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (heightLower : Nat -> Nat)
    (crossingThreshold : (Nat -> Nat) -> Nat -> Nat)
    (hwind : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (hsmall : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) -> forall k,
      let R := fkRectFixedChargeVerticalFamily r k (m k)
      let n := crossingThreshold m k
      Nat.choose R.height (n + 1) *
          ((FK.freeInfiniteVolume 2
            (fkRectCriticalP_pos (by linarith : 0 < q))
            (fkRectCriticalP_lt_one (by linarith : 0 < q))
            (by linarith : 0 < q) :
              MeasureTheory.Measure (ConfigSpace
                (Sym2 (StatMech.Lattice.Site 2)))).real
            (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) <=
        FK.cFE (fkRectCriticalP q) q ^
          (2 * R.width + R.height) / 2)
    (hwidth : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        ((fkRectFixedChargeVerticalFamily r k (m k)).width : Real) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0))
    (hthreshold : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        (crossingThreshold m k : Real) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0))
    (hheight : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop atTop)
    (hshare : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectBalancedSectorShare
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  apply fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_balancedShare
    hq r hr heightLower hwind
  · intro m hm
    exact
      tendsto_allSectorNormalization_negLog_div_height_zero_of_boundaryIncidenceAdaptiveTail
        (fun k => fkRectFixedChargeVerticalFamily r k (m k)) hq
        (crossingThreshold m) (hsmall m hm) (hwidth m hm)
        (hthreshold m hm) (hheight m hm)
  · exact hshare

set_option maxHeartbeats 800000 in




theorem
    fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_freePIMS_balancedShare
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (heightLower : Nat -> Nat)
    (hPIMS : forall k,
      fkRectBoundaryIncidencePIMSHeightLower q r k <= heightLower k)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (by linarith : 0 < q))
        (fkRectCriticalP_lt_one (by linarith : 0 < q))
        (by linarith : 0 < q) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0)
    (hwind : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (hshare : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectBalancedSectorShare
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  let hq1 : 1 <= q := by linarith
  let c := FK.cFE (fkRectCriticalP q) q
  let p := fkRectFixedChargeFreeOneArm hq1 r
  let depth := fkRectPIMSDecayDepth (c / 4) p
  let threshold : (Nat -> Nat) -> Nat -> Nat := fun m k =>
    fkRectPIMSSublinearThreshold (depth k)
      (fkRectFixedChargeVerticalFamily r k (m k)).height
  have hc0 : 0 < c := by
    exact FK.cFE_pos
      (fkRectCriticalP_pos (by linarith : 0 < q))
      (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith)
  have hc1 : c <= 1 := fkRectCritical_cFE_le_one hq1
  have hp0 : forall k, 0 <= p k := fun _ => measureReal_nonneg
  have hp1 : forall k, p k <= 1 := fun _ => measureReal_le_one
  have hp : Tendsto p atTop (nhds 0) := by
    exact tendsto_fkRectFixedChargeFreeOneArm_zero_of_percolation_zero
      hq1 r hperc
  have scheduled (m : Nat -> Nat)
      (hm : forall k, heightLower k <= m k) :=
    fkRect_pimsDecay_scheduled_binomialSmallness hc0 hc1 p hp0 hp1 hp
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).width)
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height)
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height_pos)
      (fun k => by
        change fkRectPIMSHeightLower c
            (fkRectFixedChargeVerticalFamily r k (m k)).width <=
          (fkRectFixedChargeVerticalFamily r k (m k)).height
        simp only [fkRectFixedChargeVerticalFamily_width,
          fkRectFixedChargeVerticalFamily_height]
        have hm' := (hPIMS k).trans (hm k)
        dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
        dsimp [c]
        omega)
  apply
    fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_balancedShare
      hq r hr heightLower threshold hwind
  · intro m hm k
    simpa [threshold, depth, p, c, fkRectFixedChargeFreeOneArm] using
      (scheduled m hm).1 k
  · intro m hm
    have hupper : Tendsto (fun k : Nat => (1 : Real) / k) atTop (nhds 0) :=
      (tendsto_natCast_atTop_atTop (R := Real)).const_div_atTop 1
    apply squeeze_zero' (g := fun k : Nat => (1 : Real) / k)
    · filter_upwards [] with k
      positivity
    · filter_upwards [eventually_ge_atTop 1] with k hk
      let W := (fkRectFixedChargeVerticalFamily r k (m k)).width
      let H := (fkRectFixedChargeVerticalFamily r k (m k)).height
      have hm' := (hPIMS k).trans (hm k)
      have hmul : k * W <= m k := by
        dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
        exact (Nat.le_add_right _ _).trans hm'
      have hkreal : (0 : Real) < k := by exact_mod_cast hk
      have hHreal : (0 : Real) < H := by
        exact_mod_cast (fkRectFixedChargeVerticalFamily r k (m k)).height_pos
      apply (div_le_div_iff₀ hHreal hkreal).2
      have hnat : W * k <= H := by
        have hmk : W * k <= m k := by
          simpa [Nat.mul_comm] using hmul
        exact hmk.trans (by
          dsimp [H]
          omega)
      change (W : Real) * (k : Real) <= 1 * (H : Real)
      norm_num
      exact_mod_cast hnat
    · exact hupper
  · intro m hm
    simpa [threshold, depth, p, c] using (scheduled m hm).2
  · intro m hm
    refine tendsto_atTop.2 (fun N => ?_)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hm' := (hPIMS k).trans (hm k)
    dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
    have hmk : k <= m k := by
      have hw : 1 <= (fkRectFixedChargeVerticalFamily r k 0).width :=
        (fkRectFixedChargeVerticalFamily r k 0).width_pos
      exact (Nat.le_mul_of_pos_right k hw).trans
        ((Nat.le_add_right _ _).trans hm')
    simp only [fkRectFixedChargeVerticalFamily_height]
    omega
  · exact hshare




structure FKQgt4BoundaryIncidenceScheduledSpectralGap
    (q xiInv : Real) : Prop where
  winding : forall r : Nat, 2 <= r -> forall m : Nat -> Nat,
    (forall k, fkRectBoundaryIncidencePIMSHeightLower q r k <= m k) ->
    Tendsto (fun k =>
      -Real.log
          (fkRectCriticalWindingTailMass
            (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds (((r - 1 : Nat) : Real) * xiInv))
  spectralGap : forall r : Nat, 2 <= r ->
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0)



theorem fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (by linarith : 0 < q))
        (fkRectCriticalP_lt_one (by linarith : 0 < q))
        (by linarith : 0 < q) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0)
    (hscheduled : FKQgt4BoundaryIncidenceScheduledSpectralGap q xiInv) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  obtain ⟨heightLower, hPIMS, hnormalization⟩ :=
    exists_fkRectBalancedNormalization_spectralHeightLower hq r hperc
      (hscheduled.spectralGap r hr)
  apply fkQgt4_fixedCharge_bound_of_uniformDiagonalLimitsAbove
    hq r hr heightLower
  · intro m hm
    apply hscheduled.winding r hr m
    intro k
    exact (hPIMS k).trans (hm k)
  · exact hnormalization



theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap
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
    (hscheduled : FKQgt4BoundaryIncidenceScheduledSpectralGap q
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge
    hq hhard hcross
  intro r hr
  apply fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap hq r hr
  · exact
      fkQgt4CriticalFree_percolation_zero_of_evenTwoByOneCrossingFloor
        hq hhard hcross
  · exact hscheduled

set_option maxHeartbeats 800000 in


theorem
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap
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
    (hscheduled : FKQgt4BoundaryIncidenceScheduledSpectralGap q
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
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
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap
      hq hhard hcross hscheduled

end

end StatMech.FrontierD
