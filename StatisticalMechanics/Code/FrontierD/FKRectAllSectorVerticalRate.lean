/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryConnectivityTransfer
import Code.FrontierD.FKRectBalancedSectorThermodynamicBridge
import Code.FrontierD.SixVertexBalancedShareVerticalRate








open Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem fkRectFixedChargeVerticalFamily_criticalReducedZ_eq_boundaryTransfer
    (r k m : Nat) (q : Real) :
    fkRectCriticalReducedZ (fkRectFixedChargeVerticalFamily r k m) q =
      fkRectBoundaryTransferReducedZ
        (fkRectFixedChargeVerticalFamily r k m).width_pos q (m + 1) := by
  apply fkRectCriticalReducedZ_eq_boundaryTransferReducedZ
  simp [fkRectFixedChargeVerticalFamily_height]



theorem exists_fkRectFixedChargeVerticalFamily_criticalReducedZ_log_div_height_tendsto
    (r k : Nat) {q : Real} (hq : 0 < q) :
    ∃ rate : Real, Tendsto (fun m : Nat =>
      Real.log (fkRectCriticalReducedZ
        (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
      atTop (nhds rate) := by
  obtain ⟨rate, hrate⟩ :=
    exists_fkRectBoundaryTransferReducedZ_log_div_tendsto
      (fkRectFixedChargeVerticalFamily r k 0).width_pos hq
  have hshift : Tendsto (fun m : Nat =>
      Real.log (fkRectBoundaryTransferReducedZ
        (fkRectFixedChargeVerticalFamily r k 0).width_pos q (m + 1)) /
          ((m + 1 : Nat) : Real)) atTop (nhds rate) := by
    convert hrate.comp (tendsto_add_atTop_nat 1) using 1
  have hratioBase := tendsto_natCast_div_natCast_add 1
  have hratioShift : Tendsto (fun m : Nat =>
      ((m + 1 : Nat) : Real) / (1 + (m + 1 : Nat) : Nat))
      atTop (nhds 1) := by
    convert hratioBase.comp (tendsto_add_atTop_nat 1) using 1
  have hratio : Tendsto (fun m : Nat =>
      ((m + 1 : Nat) : Real) /
        (fkRectFixedChargeVerticalFamily r k m).height)
      atTop (nhds ((1 : Real) / 2)) := by
    have hhalfConst : Tendsto (fun _ : Nat => ((1 : Real) / 2))
        atTop (nhds ((1 : Real) / 2)) := tendsto_const_nhds
    have hhalf := hhalfConst.mul hratioShift
    convert hhalf using 1
    · funext m
      simp only [fkRectFixedChargeVerticalFamily_height, Function.comp_apply,
        Nat.cast_mul, Nat.cast_ofNat]
      field_simp
      ring
    · ring
  have hproduct : Tendsto (fun m : Nat =>
      (Real.log (fkRectBoundaryTransferReducedZ
          (fkRectFixedChargeVerticalFamily r k 0).width_pos q (m + 1)) /
        ((m + 1 : Nat) : Real)) *
      (((m + 1 : Nat) : Real) /
        (fkRectFixedChargeVerticalFamily r k m).height))
      atTop (nhds (rate / 2)) := by
    simpa [div_eq_mul_inv] using hshift.mul hratio
  refine ⟨rate / 2, hproduct.congr' ?_⟩
  filter_upwards [] with m
  rw [fkRectFixedChargeVerticalFamily_criticalReducedZ_eq_boundaryTransfer]
  simp only [fkRectFixedChargeVerticalFamily_width]
  have hm : (0 : Real) < (m + 1 : Nat) := by positivity
  have hh : (0 : Real) <
      (fkRectFixedChargeVerticalFamily r k m).height := by
    exact_mod_cast (fkRectFixedChargeVerticalFamily r k m).height_pos
  field_simp



theorem fkRectFixedChargeVerticalFamily_arrowPartition_log_div_height_tendsto
    (r k : Nat) {q : Real} (hq : 4 < q) :
    Tendsto (fun m : Nat =>
      Real.log (sixVertexTorusArrowPartitionSum
        (fkRectFixedChargeVerticalFamily r k m).medialTorus
        (fkQgt4SixVertexWeight q)) /
          (fkRectFixedChargeVerticalFamily r k m).height)
      atTop (nhds (Real.log (sixVertexWidthTopEigenvalue
        (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)))) := by
  have hc : 0 < fkQgt4SixVertexWeight q := by
    linarith [two_lt_fkQgt4SixVertexWeight hq]
  have hheight : Tendsto (fun m : Nat => 2 * (m + 2)) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 ⟨N, fun m hm => by omega⟩
  have h := (sixVertexFixedWidth_log_partition_div_height_tendsto
    (sixVertexFourWidth r (k + 1)) hc).comp hheight
  apply h.congr'
  filter_upwards [] with m
  rw [sixVertexTorusArrowPartitionSum_eq_fixedWidthPartitionSum]
  simp only [fkRectFixedChargeVerticalFamily_medialWidth,
    fkRectFixedChargeVerticalFamily_medialHeight,
    fkRectFixedChargeVerticalFamily_height, Function.comp_apply]



theorem fkRectFixedChargeVerticalFamily_allSector_negLog_div_height_eq
    (r k m : Nat) {q : Real} (hq : 4 < q) :
    -Real.log (fkRectAllSectorNormalization
        (fkRectFixedChargeVerticalFamily r k m) q) /
        (fkRectFixedChargeVerticalFamily r k m).height =
      Real.log (fkRectCriticalReducedZ
          (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height -
        Real.log (sixVertexTorusArrowPartitionSum
          (fkRectFixedChargeVerticalFamily r k m).medialTorus
          (fkQgt4SixVertexWeight q)) /
          (fkRectFixedChargeVerticalFamily r k m).height -
        ((fkRectFixedChargeVerticalFamily r k m).width : Real) *
          Real.log (Real.sqrt q) := by
  let R := fkRectFixedChargeVerticalFamily r k m
  let s := Real.sqrt q
  let B := sixVertexTorusArrowPartitionSum R.medialTorus
    (fkQgt4SixVertexWeight q)
  let Z := fkRectCriticalReducedZ R q
  have hs : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hZ : 0 < Z := fkRectCriticalReducedZ_pos R (by linarith)
  have hc : 0 < fkQgt4SixVertexWeight q := by
    linarith [two_lt_fkQgt4SixVertexWeight hq]
  have hB : 0 < B := by
    dsimp [B]
    rw [sixVertexTorusArrowPartitionSum_eq_fixedWidthPartitionSum]
    exact sixVertexFixedWidthPartitionSum_pos R.medialTorus.width
      R.medialTorus.height R.medialTorus.height_pos hc
  have hheight : (R.height : Real) ≠ 0 := by
    exact_mod_cast R.height_pos.ne'
  change -Real.log (s ^ (R.width * R.height) * (B / Z)) / R.height = _
  rw [Real.log_mul (pow_ne_zero _ hs.ne') (div_ne_zero hB.ne' hZ.ne'),
    Real.log_pow, Real.log_div hB.ne' hZ.ne']
  change _ = Real.log Z / R.height - Real.log B / R.height -
    (R.width : Real) * Real.log s
  push_cast
  field_simp
  ring



theorem exists_fkRectAllSectorNormalization_vertical_negLogRate
    (r k : Nat) {q : Real} (hq : 4 < q) :
    ∃ rate : Real, Tendsto (fun m : Nat =>
      -Real.log (fkRectAllSectorNormalization
        (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
      atTop (nhds rate) := by
  obtain ⟨fkRate, hfk⟩ :=
    exists_fkRectFixedChargeVerticalFamily_criticalReducedZ_log_div_height_tendsto
      r k (by linarith)
  have hsv := fkRectFixedChargeVerticalFamily_arrowPartition_log_div_height_tendsto
    r k hq
  let widthCost := ((fkRectFixedChargeVerticalFamily r k 0).width : Real) *
    Real.log (Real.sqrt q)
  refine ⟨fkRate - Real.log (sixVertexWidthTopEigenvalue
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) - widthCost, ?_⟩
  have hconst : Tendsto (fun _ : Nat => widthCost) atTop (nhds widthCost) :=
    tendsto_const_nhds
  have hlimit := (hfk.sub hsv).sub hconst
  apply hlimit.congr'
  filter_upwards [] with m
  rw [fkRectFixedChargeVerticalFamily_allSector_negLog_div_height_eq r k m hq]
  rfl


noncomputable def fkRectAllSectorNormalizationVerticalRate
    {q : Real} (hq : 4 < q) (r k : Nat) : Real :=
  Classical.choose
    (exists_fkRectAllSectorNormalization_vertical_negLogRate r k hq)

theorem fkRectAllSectorNormalization_vertical_negLog_tendsto_rate
    {q : Real} (hq : 4 < q) (r k : Nat) :
    Tendsto (fun m : Nat =>
      -Real.log (fkRectAllSectorNormalization
        (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
      atTop (nhds (fkRectAllSectorNormalizationVerticalRate hq r k)) :=
  Classical.choose_spec
    (exists_fkRectAllSectorNormalization_vertical_negLogRate r k hq)

end

end StatMech.FrontierD
