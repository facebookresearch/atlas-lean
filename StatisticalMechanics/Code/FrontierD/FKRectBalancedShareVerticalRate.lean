/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectBalancedSectorThermodynamicBridge
import Code.FrontierD.SixVertexBalancedShareGluing
import Code.FrontierD.SixVertexBalancedShareVerticalRate
import Code.FrontierD.SixVertexCentralSectorDominance

open Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem fkRectFixedChargeVerticalFamily_balancedShare_eq_traceShare
    (r k m : Nat) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily r k m) q =
      sixVertexBalancedTraceShare
        (fkRectFixedChargeVerticalFamily r k m).medialTorus.width
        (fkRectFixedChargeVerticalFamily r k m).medialTorus.height
        (fkQgt4SixVertexWeight q) := by
  rw [fkRectBalancedSectorShare_eq_sixVertexRatio _ hq,
    sixVertexTorusFixedChargePartitionSum_eq_sectorTrace,
    sixVertexTorusArrowPartitionSum_eq_fixedWidthPartitionSum]
  unfold sixVertexBalancedTraceShare
  simp only [Nat.sub_zero]



theorem fkRectBalancedSectorShare_vertical_negLog_tendsto
    {q : Real} (hq : 4 < q) (k : Nat) :
    Tendsto (fun m =>
      -Real.log (fkRectBalancedSectorShare
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height)
      atTop
      (nhds (Real.log (sixVertexWidthTopEigenvalue
          (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q)) -
        Real.log (sixVertexLambdaAlongFour
          (fkQgt4SixVertexWeight q) 0 (k + 1)))) := by
  have hindex : Tendsto (fun m : Nat => 2 * (m + 2)) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 <| ⟨N, fun m hm => by omega⟩
  have h := (sixVertexBalancedTraceShare_negLog_div_height_tendsto
    (sixVertexFourWidth 0 (k + 1))
    (sixVertexFourWidth_even 0 (k + 1))
    (by linarith [two_lt_fkQgt4SixVertexWeight hq] :
      0 < fkQgt4SixVertexWeight q)).comp hindex
  apply h.congr'
  filter_upwards [] with m
  rw [fkRectFixedChargeVerticalFamily_balancedShare_eq_traceShare 0 k m hq]
  simp only [fkRectFixedChargeVerticalFamily_medialWidth,
    fkRectFixedChargeVerticalFamily_medialHeight,
    fkRectFixedChargeVerticalFamily_height, Function.comp_apply]



theorem fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_central_max
    {q : Real} (hq : 4 < q) (k : Nat)
    (hcentral :
      sixVertexWidthTopEigenvalue (sixVertexFourWidth 0 (k + 1))
          (fkQgt4SixVertexWeight q) =
        sixVertexLambdaAlongFour (fkQgt4SixVertexWeight q) 0 (k + 1)) :
    Tendsto (fun m =>
      -Real.log (fkRectBalancedSectorShare
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height)
      atTop (nhds 0) := by
  simpa [hcentral] using
    fkRectBalancedSectorShare_vertical_negLog_tendsto hq k




theorem
    fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_strictLowerHalf
    {q : Real} (hq : 4 < q) (k : Nat)
    (hdom : SixVertexStrictLowerHalfDominance
      (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q)) :
    Tendsto (fun m =>
      -Real.log (fkRectBalancedSectorShare
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height)
      atTop (nhds 0) := by
  have hc : 0 < fkQgt4SixVertexWeight q := by
    linarith [two_lt_fkQgt4SixVertexWeight hq]
  have htop := sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalf
    (sixVertexFourWidth 0 (k + 1))
    (sixVertexFourWidth_even 0 (k + 1))
    (sixVertexFourWidth_pos 0 (k + 1)) hc hdom
  apply fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_central_max
    hq k
  simpa [sixVertexLambdaAlongFour, sixVertexLambda] using htop




theorem
    fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_strictLowerHalfAboveOne
    {q : Real} (hq : 4 < q) (k : Nat)
    (hdom : SixVertexStrictLowerHalfDominanceAboveOne
      (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q)) :
    Tendsto (fun m =>
      -Real.log (fkRectBalancedSectorShare
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height)
      atTop (nhds 0) := by
  have hc : 0 < fkQgt4SixVertexWeight q := by
    linarith [two_lt_fkQgt4SixVertexWeight hq]
  have hc2 : 2 <= fkQgt4SixVertexWeight q :=
    (two_lt_fkQgt4SixVertexWeight hq).le
  have htop :=
    sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalfAboveOne
      (sixVertexFourWidth 0 (k + 1))
      (sixVertexFourWidth_even 0 (k + 1)) (by
        simp [sixVertexFourWidth]) hc hc2 hdom
  apply fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_central_max
    hq k
  simpa [sixVertexLambdaAlongFour, sixVertexLambda] using htop




theorem fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero
    {q : Real} (hq : 4 < q) (k : Nat)
    (hcentral :
      sixVertexWidthTopEigenvalue (sixVertexFourWidth 0 (k + 1))
          (fkQgt4SixVertexWeight q) =
        sixVertexLambdaAlongFour (fkQgt4SixVertexWeight q) 0 (k + 1))
    (hall : Tendsto (fun m =>
      -Real.log (fkRectAllSectorNormalization
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height)
      atTop (nhds 0)) :
    Tendsto (fun m =>
      -Real.log (fkRectBalancedSectorNormalization
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height)
      atTop (nhds 0) := by
  have hshare :=
    fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_central_max
      hq k hcentral
  have hadd := hall.add hshare
  have heq : (fun m =>
      -Real.log (fkRectBalancedSectorNormalization
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height) =
      (fun m =>
        -Real.log (fkRectAllSectorNormalization
            (fkRectFixedChargeVerticalFamily 0 k m) q) /
          (fkRectFixedChargeVerticalFamily 0 k m).height +
        -Real.log (fkRectBalancedSectorShare
            (fkRectFixedChargeVerticalFamily 0 k m) q) /
          (fkRectFixedChargeVerticalFamily 0 k m).height) := by
    funext m
    rw [balancedNormalization_negLog_eq_all_add_share
      (fkRectFixedChargeVerticalFamily 0 k m) hq]
    ring
  rw [heq]
  simpa using hadd



theorem
    fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero_of_strictLowerHalf
    {q : Real} (hq : 4 < q) (k : Nat)
    (hdom : SixVertexStrictLowerHalfDominance
      (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q))
    (hall : Tendsto (fun m =>
      -Real.log (fkRectAllSectorNormalization
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height)
      atTop (nhds 0)) :
    Tendsto (fun m =>
      -Real.log (fkRectBalancedSectorNormalization
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height)
      atTop (nhds 0) := by
  have hshare :=
    fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_strictLowerHalf
      hq k hdom
  have hadd := hall.add hshare
  have heq : (fun m =>
      -Real.log (fkRectBalancedSectorNormalization
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height) =
      (fun m =>
        -Real.log (fkRectAllSectorNormalization
            (fkRectFixedChargeVerticalFamily 0 k m) q) /
          (fkRectFixedChargeVerticalFamily 0 k m).height +
        -Real.log (fkRectBalancedSectorShare
            (fkRectFixedChargeVerticalFamily 0 k m) q) /
          (fkRectFixedChargeVerticalFamily 0 k m).height) := by
    funext m
    rw [balancedNormalization_negLog_eq_all_add_share
      (fkRectFixedChargeVerticalFamily 0 k m) hq]
    ring
  rw [heq]
  simpa using hadd



theorem
    fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero_of_strictLowerHalfAboveOne
    {q : Real} (hq : 4 < q) (k : Nat)
    (hdom : SixVertexStrictLowerHalfDominanceAboveOne
      (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q))
    (hall : Tendsto (fun m =>
      -Real.log (fkRectAllSectorNormalization
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height)
      atTop (nhds 0)) :
    Tendsto (fun m =>
      -Real.log (fkRectBalancedSectorNormalization
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height)
      atTop (nhds 0) := by
  have hshare :=
    fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_strictLowerHalfAboveOne
      hq k hdom
  have hadd := hall.add hshare
  have heq : (fun m =>
      -Real.log (fkRectBalancedSectorNormalization
          (fkRectFixedChargeVerticalFamily 0 k m) q) /
        (fkRectFixedChargeVerticalFamily 0 k m).height) =
      (fun m =>
        -Real.log (fkRectAllSectorNormalization
            (fkRectFixedChargeVerticalFamily 0 k m) q) /
          (fkRectFixedChargeVerticalFamily 0 k m).height +
        -Real.log (fkRectBalancedSectorShare
            (fkRectFixedChargeVerticalFamily 0 k m) q) /
          (fkRectFixedChargeVerticalFamily 0 k m).height) := by
    funext m
    rw [balancedNormalization_negLog_eq_all_add_share
      (fkRectFixedChargeVerticalFamily 0 k m) hq]
    ring
  rw [heq]
  simpa using hadd

end

end StatMech.FrontierD
