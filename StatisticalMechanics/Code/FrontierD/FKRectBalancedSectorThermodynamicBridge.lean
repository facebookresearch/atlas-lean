/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierD.FKRectBalancedSectorNormalization
import Code.FrontierD.FKRectNoLoopNormalization
import Code.FrontierD.FKQgt4CorrelationReduction
import Code.FrontierD.SixVertexBalancedShareGluing
import Code.FrontierD.SixVertexBetheCanonicalOddWallisLimit

open Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem le_negLog_div_of_le_exp_neg_mul
    {mass height rate : Real} (hmass : 0 < mass) (hheight : 0 < height)
    (hupper : mass <= Real.exp (-rate * height)) :
    rate <= -Real.log mass / height := by
  have hlog : Real.log mass <= -rate * height := by
    calc
      Real.log mass <= Real.log (Real.exp (-rate * height)) :=
        Real.log_le_log hmass hupper
      _ = -rate * height := Real.log_exp _
  rw [le_div_iff₀ hheight]
  linarith



def fkRectFixedChargeVerticalFamily (r k m : Nat) : FKRectTorus where
  width := 2 * (r + k + 2)
  height := 2 * (m + 2)
  width_gt_two := by omega
  height_gt_two := by omega
  height_even := ⟨m + 2, by omega⟩

@[simp] theorem fkRectFixedChargeVerticalFamily_width
    (r k m : Nat) :
    (fkRectFixedChargeVerticalFamily r k m).width = 2 * (r + k + 2) := rfl

@[simp] theorem fkRectFixedChargeVerticalFamily_height
    (r k m : Nat) :
    (fkRectFixedChargeVerticalFamily r k m).height = 2 * (m + 2) := rfl

@[simp] theorem fkRectFixedChargeVerticalFamily_medialWidth
    (r k m : Nat) :
    (fkRectFixedChargeVerticalFamily r k m).medialTorus.width =
      sixVertexFourWidth r (k + 1) := by
  change 2 * (2 * (r + k + 2)) = 4 * (r + (k + 1) + 1)
  omega

@[simp] theorem fkRectFixedChargeVerticalFamily_medialHeight
    (r k m : Nat) :
    (fkRectFixedChargeVerticalFamily r k m).medialTorus.height =
      2 * (m + 2) := rfl

theorem fkRectFixedChargeVerticalFamily_charge_le
    (r k m : Nat) :
    r ≤ (fkRectFixedChargeVerticalFamily r k m).medialTorus.width / 2 := by
  rw [fkRectFixedChargeVerticalFamily_medialWidth]
  exact sixVertexFourWidth_charge_le r (k + 1)

theorem tendsto_fkRectFixedChargeVerticalFamily_height :
    Tendsto (fun m =>
      (fkRectFixedChargeVerticalFamily 0 0 m).height) atTop atTop := by
  refine tendsto_atTop.2 (fun N => ?_)
  exact eventually_atTop.2 ⟨N, fun m hm => by
    simp only [fkRectFixedChargeVerticalFamily_height]
    omega⟩



theorem exists_nat_diagonal_tendsto_above
    (f : Nat -> Nat -> Real) (a : Nat -> Real) {L : Real}
    (lower : Nat -> Nat)
    (hvertical : forall k, Tendsto (f k) atTop (nhds (a k)))
    (hhorizontal : Tendsto a atTop (nhds L)) :
    exists m : Nat -> Nat, (forall k, lower k <= m k) /\
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
  let m : Nat -> Nat := fun k => max (lower k) (M k)
  have hm (k : Nat) : lower k <= m k := le_max_left _ _
  have herr (k : Nat) :
      dist (f k (m k)) (a k) <= (1 : Real) / (k + 1) := by
    exact (hM k (m k) (le_max_right _ _)).le
  have heps : Tendsto (fun k : Nat => (1 : Real) / (k + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have haDist : Tendsto (fun k => dist (a k) L) atTop (nhds 0) :=
    (tendsto_iff_dist_tendsto_zero).1 hhorizontal
  have hdist : Tendsto (fun k => dist (f k (m k)) L) atTop (nhds 0) := by
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
  exact ⟨m, hm, (tendsto_iff_dist_tendsto_zero).2 hdist⟩


theorem exists_nat_diagonal_tendsto
    (f : Nat -> Nat -> Real) (a : Nat -> Real) {L : Real}
    (hvertical : forall k, Tendsto (f k) atTop (nhds (a k)))
    (hhorizontal : Tendsto a atTop (nhds L)) :
    exists m : Nat -> Nat, (forall k, k <= m k) /\
      Tendsto (fun k => f k (m k)) atTop (nhds L) :=
  exists_nat_diagonal_tendsto_above f a (fun k => k)
    hvertical hhorizontal



theorem fkRectFixedCharge_vertical_negLogRatio_tendsto
    {c : Real} (hc : 0 < c) (r k : Nat) :
    Tendsto (fun m =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k m).medialTorus r
                (fkRectFixedChargeVerticalFamily_charge_le r k m) c /
            sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k m).medialTorus 0
                (Nat.zero_le _) c) /
        (fkRectFixedChargeVerticalFamily r k m).height)
      atTop
      (nhds (-sixVertexFixedChargeLogRatio c r (k + 1))) := by
  have hindex : Tendsto (fun m : Nat => 2 * (m + 2)) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 ⟨N, fun m hm => by omega⟩
  have h := (sixVertexFixedChargeTraceLogRatio_div_height_tendsto
    hc r (k + 1)).comp hindex
  have hneg := h.neg
  apply hneg.congr'
  filter_upwards [] with m
  rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace,
    sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
  rw [fkRectFixedChargeVerticalFamily_medialWidth r k m]
  simp only [fkRectFixedChargeVerticalFamily_medialHeight,
    fkRectFixedChargeVerticalFamily_height, Function.comp_apply,
    Nat.sub_zero, neg_div]



theorem tendsto_sixVertexFixedCharge_negLogRatio_gap
    {c : Real} (hc : 2 < c) (r : Nat) (hr : 1 ≤ r) :
    Tendsto (fun k => -sixVertexFixedChargeLogRatio c r (k + 1))
      atTop
      (nhds ((r : Real) * sixVertexAntiferroelectricGapRate
        (sixVertexAntiferroelectricLambda c))) := by
  have htransfer := (sixVertexAntiferroelectricTransferConclusion hc).2 r hr
  have hlog := (sixVertexFixedChargeRatio_tendsto_iff_logRatio
    (by linarith : 0 < c) r).1 htransfer
  have hshift := hlog.comp (tendsto_add_atTop_nat 1)
  have hneg := hshift.neg
  convert hneg using 1 <;> ring



theorem tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap
    {q : Real} (hq : 4 < q) (r : Nat) (hr : 1 ≤ r) :
    Tendsto (fun k =>
      -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) r (k + 1))
      atTop (nhds ((r : Real) * fkQgt4SixVertexGapRate q)) := by
  simpa [fkQgt4SixVertexGapRate] using
    tendsto_sixVertexFixedCharge_negLogRatio_gap
      (two_lt_fkQgt4SixVertexWeight hq) r hr




theorem exists_fkQgt4_fixedCharge_diagonal_tendsto_gap_above
    {q : Real} (hq : 4 < q) (r : Nat) (hr : 1 <= r)
    (lower : Nat -> Nat) :
    exists m : Nat -> Nat, (forall k, lower k <= m k) /\
      Tendsto (fun k =>
        -Real.log
            (sixVertexTorusFixedChargePartitionSum
                  (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r
                  (fkRectFixedChargeVerticalFamily_charge_le r k (m k))
                  (fkQgt4SixVertexWeight q) /
              sixVertexTorusFixedChargePartitionSum
                  (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0
                  (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds ((r : Real) * fkQgt4SixVertexGapRate q)) := by
  apply exists_nat_diagonal_tendsto_above
    (fun k m =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k m).medialTorus r
                (fkRectFixedChargeVerticalFamily_charge_le r k m)
                (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k m).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (fkRectFixedChargeVerticalFamily r k m).height)
    (fun k => -sixVertexFixedChargeLogRatio
      (fkQgt4SixVertexWeight q) r (k + 1))
    lower
  · intro k
    exact fkRectFixedCharge_vertical_negLogRatio_tendsto
      (by linarith [two_lt_fkQgt4SixVertexWeight hq] :
        0 < fkQgt4SixVertexWeight q) r k
  · exact tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap hq r hr


theorem exists_fkQgt4_fixedCharge_diagonal_tendsto_gap
    {q : Real} (hq : 4 < q) (r : Nat) (hr : 1 <= r) :
    exists m : Nat -> Nat, (forall k, k <= m k) /\
      Tendsto (fun k =>
        -Real.log
            (sixVertexTorusFixedChargePartitionSum
                  (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r
                  (fkRectFixedChargeVerticalFamily_charge_le r k (m k))
                  (fkQgt4SixVertexWeight q) /
              sixVertexTorusFixedChargePartitionSum
                  (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0
                  (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds ((r : Real) * fkQgt4SixVertexGapRate q)) :=
  exists_fkQgt4_fixedCharge_diagonal_tendsto_gap_above
    hq r hr (fun k => k)



theorem fkQgt4_fixedCharge_bound_of_diagonalLimits
    {q xiInv : Real} (hq : 4 < q) (r : Nat)
    (m : Nat -> Nat)
    (hwind : Tendsto (fun k =>
      -Real.log
          (fkRectCriticalWindingTailMass
            (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (hcharge : Tendsto (fun k =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r
                (fkRectFixedChargeVerticalFamily_charge_le r k (m k))
                (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds ((r : Real) * fkQgt4SixVertexGapRate q)))
    (hnormalization : Tendsto (fun k =>
      -Real.log
          (fkRectBalancedSectorNormalization
            (fkRectFixedChargeVerticalFamily r k (m k)) q) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  have hle : ∀ᶠ k in atTop,
      -Real.log
          (fkRectCriticalWindingTailMass
            (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height <=
      -Real.log
          (sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r
                (fkRectFixedChargeVerticalFamily_charge_le r k (m k))
                (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height +
      -Real.log
          (fkRectBalancedSectorNormalization
            (fkRectFixedChargeVerticalFamily r k (m k)) q) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height := by
    filter_upwards [] with k
    exact windingTail_negLogRate_le_fixedCharge_add_normalizationDefect
      (fkRectFixedChargeVerticalFamily r k (m k)) hq r
        (fkRectFixedChargeVerticalFamily_charge_le r k (m k))
  have hlimit := le_of_tendsto_of_tendsto hwind
    (hcharge.add hnormalization) hle
  simpa using hlimit



theorem fkQgt4_fixedCharge_bound_of_diagonalWindingLowerBound
    {q xiInv : Real} (hq : 4 < q) (r : Nat)
    (m : Nat -> Nat) (windingLower : Nat -> Real)
    (hwindLower : Tendsto windingLower atTop
      (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (hwindBound : ∀ᶠ k in atTop,
      windingLower k <=
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
    (hcharge : Tendsto (fun k =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r
                (fkRectFixedChargeVerticalFamily_charge_le r k (m k))
                (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds ((r : Real) * fkQgt4SixVertexGapRate q)))
    (hnormalization : Tendsto (fun k =>
      -Real.log
          (fkRectBalancedSectorNormalization
            (fkRectFixedChargeVerticalFamily r k (m k)) q) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  have hfinite : ∀ᶠ k in atTop,
      -Real.log
          (fkRectCriticalWindingTailMass
            (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height <=
      -Real.log
          (sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r
                (fkRectFixedChargeVerticalFamily_charge_le r k (m k))
                (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum
                (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height +
      -Real.log
          (fkRectBalancedSectorNormalization
            (fkRectFixedChargeVerticalFamily r k (m k)) q) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height := by
    filter_upwards [] with k
    exact windingTail_negLogRate_le_fixedCharge_add_normalizationDefect
      (fkRectFixedChargeVerticalFamily r k (m k)) hq r
        (fkRectFixedChargeVerticalFamily_charge_le r k (m k))
  have hbound : ∀ᶠ k in atTop,
      windingLower k <=
        (-Real.log
            (sixVertexTorusFixedChargePartitionSum
                  (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r
                  (fkRectFixedChargeVerticalFamily_charge_le r k (m k))
                  (fkQgt4SixVertexWeight q) /
              sixVertexTorusFixedChargePartitionSum
                  (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0
                  (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height) +
        (-Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height) := by
    filter_upwards [hwindBound, hfinite] with k hlower hupper
    exact hlower.trans hupper
  have hlimit := le_of_tendsto_of_tendsto hwindLower
    (hcharge.add hnormalization) hbound
  simpa using hlimit




theorem fkQgt4_fixedCharge_bound_of_uniformDiagonalLimitsAbove
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
    (hnormalization : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  obtain ⟨m, hm, hcharge⟩ :=
    exists_fkQgt4_fixedCharge_diagonal_tendsto_gap_above
      hq r (by omega) heightLower
  exact fkQgt4_fixedCharge_bound_of_diagonalLimits hq r m
    (hwind m hm) hcharge (hnormalization m hm)




theorem fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_fourCopy
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
    (hfourCopy : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        fkRectFourCopyShareCost
            (fkRectFixedChargeVerticalFamily r k (m k)) q /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  apply fkQgt4_fixedCharge_bound_of_uniformDiagonalLimitsAbove
    hq r hr heightLower hwind
  intro m hm
  exact tendsto_balancedNormalization_negLog_div_height_zero_of_all_and_fourCopy
    (fun k => fkRectFixedChargeVerticalFamily r k (m k)) hq
      (hnoLoop m hm) (hfourCopy m hm)




theorem fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_zeroTurnTail_fourCopy
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (heightLower : Nat -> Nat)
    (threshold : (Nat -> Nat) -> Nat -> Nat)
    (hwind : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (htail : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) -> forall k,
      fkRectCriticalZeroTurnAboveMass
          (fkRectFixedChargeVerticalFamily r k (m k)) q (threshold m k) <=
        (1 : Real) / 2)
    (hthreshold : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        ((threshold m k : Nat) : Real) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0))
    (hheight : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop atTop)
    (hfourCopy : forall m : Nat -> Nat,
      (forall k, heightLower k <= m k) ->
      Tendsto (fun k =>
        fkRectFourCopyShareCost
            (fkRectFixedChargeVerticalFamily r k (m k)) q /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  apply fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_fourCopy
    hq r hr heightLower hwind
  · intro m hm
    exact tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_tail
      (fun k => fkRectFixedChargeVerticalFamily r k (m k)) hq
        (threshold m) (htail m hm) (hthreshold m hm) (hheight m hm)
  · exact hfourCopy


theorem fkQgt4_fixedCharge_bound_of_uniformDiagonalLimits
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (hwind : forall m : Nat -> Nat, (forall k, k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (hnormalization : forall m : Nat -> Nat, (forall k, k <= m k) ->
      Tendsto (fun k =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q :=
  fkQgt4_fixedCharge_bound_of_uniformDiagonalLimitsAbove
    hq r hr (fun k => k) hwind hnormalization

set_option maxHeartbeats 800000 in






theorem fkQgt4_fixedCharge_bound_of_windingTail_iteratedLimits
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (windingRate : Nat -> Real)
    (normalizationRate : Nat -> Real)
    (hwindVertical : forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k m) q r) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (windingRate k)))
    (hwindHorizontal : Tendsto windingRate atTop
      (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (hnormalizationVertical : forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (normalizationRate k)))
    (hnormalizationHorizontal : Tendsto normalizationRate atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  have hfixedWidth (k : Nat) :
      windingRate k <=
        -sixVertexFixedChargeLogRatio
          (fkQgt4SixVertexWeight q) r (k + 1) + normalizationRate k := by
    exact windingTailRate_le_fixedChargeRate_add_normalizationRate_of_tendsto
      (fun m => fkRectFixedChargeVerticalFamily r k m)
      (q := q) (windingRate := windingRate k)
      (chargeRate := -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) r (k + 1))
      (normalizationRate := normalizationRate k)
      hq r
      (fun m => fkRectFixedChargeVerticalFamily_charge_le r k m)
      (hwindVertical k)
      (fkRectFixedCharge_vertical_negLogRatio_tendsto
        (by linarith [two_lt_fkQgt4SixVertexWeight hq] :
          0 < fkQgt4SixVertexWeight q) r k)
      (hnormalizationVertical k)
  have hle := le_of_tendsto_of_tendsto hwindHorizontal
    ((tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap hq r (by omega)).add
      hnormalizationHorizontal)
    (Filter.Eventually.of_forall hfixedWidth)
  simpa using hle

end

end StatMech.FrontierD
