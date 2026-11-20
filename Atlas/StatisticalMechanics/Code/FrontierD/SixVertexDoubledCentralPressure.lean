/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierD.SixVertexBalancedShareVerticalRate
import Code.FrontierD.SixVertexBetheCanonicalPerronClosed
import Code.FrontierD.FKQgt4ParameterBridge

open Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexFullTrace_pow_four_le_boundary_mul_doubledCentralTrace
    (N M : Nat) (hN : 0 < N) (hM : 0 < M)
    (hNeven : Even N) (hMeven : Even M)
    {c : Real} (hc : 0 <= c) :
    sixVertexFixedWidthPartitionSum N M c ^ 4 <=
      (2 : Real) ^ (4 * (N + M)) *
        Matrix.trace
          (sixVertexSectorTransfer (N + N) ((N + N) / 2) c ^ (M + M)) := by
  let T : EvenTorus :=
    { width := N
      height := M
      width_pos := hN
      height_pos := hM
      width_even := hNeven
      height_even := hMeven }
  have h :=
    sixVertexTorusArrowPartitionSum_pow_four_le_boundaryFactor_mul_balanced
      T hc
  have hbalanced : sixVertexRectangleBalancedPartitionSum
      (T.width + T.width) (T.height + T.height) c =
        Matrix.trace (sixVertexSectorTransfer
          (T.width + T.width) ((T.width + T.width) / 2) c ^
            (T.height + T.height)) := by
    simpa only [EvenTorus.double] using
      sixVertexRectangleBalancedPartitionSum_eq_halfFilledTrace T.double c
  rw [sixVertexTorusArrowPartitionSum_eq_fixedWidthPartitionSum,
    hbalanced] at h
  simpa [T] using h



theorem sixVertexDoubledCentralTrace_le_fullTrace
    (N M : Nat) (hN : 0 < N) (hM : 0 < M)
    (hNeven : Even N) (hMeven : Even M)
    {c : Real} (hc : 0 <= c) :
    Matrix.trace
        (sixVertexSectorTransfer (N + N) ((N + N) / 2) c ^ (M + M)) <=
      sixVertexFixedWidthPartitionSum (N + N) (M + M) c := by
  let T : EvenTorus :=
    { width := N
      height := M
      width_pos := hN
      height_pos := hM
      width_even := hNeven
      height_even := hMeven }
  have h := sixVertexTorusArrowPartition_balancedBoundaryControl T hc
  have hbalanced : sixVertexRectangleBalancedPartitionSum
      (T.width + T.width) (T.height + T.height) c =
        Matrix.trace (sixVertexSectorTransfer
          (T.width + T.width) ((T.width + T.width) / 2) c ^
            (T.height + T.height)) := by
    simpa only [EvenTorus.double] using
      sixVertexRectangleBalancedPartitionSum_eq_halfFilledTrace T.double c
  have hfull : sixVertexTorusArrowPartitionSum T.double c =
      sixVertexFixedWidthPartitionSum
        (T.width + T.width) (T.height + T.height) c := by
    simpa only [EvenTorus.double] using
      sixVertexTorusArrowPartitionSum_eq_fixedWidthPartitionSum T.double c
  rw [hbalanced, hfull] at h
  simpa [T, EvenTorus.double] using h.1



theorem four_mul_log_sixVertexFullTrace_le_boundary_add_log_doubledCentral
    (N M : Nat) (hN : 0 < N) (hM : 0 < M)
    (hNeven : Even N) (hMeven : Even M)
    {c : Real} (hc : 0 < c) :
    4 * Real.log (sixVertexFixedWidthPartitionSum N M c) <=
      (4 * (N + M) : Nat) * Real.log 2 +
        Real.log (Matrix.trace
          (sixVertexSectorTransfer (N + N) ((N + N) / 2) c ^ (M + M))) := by
  let Z := sixVertexFixedWidthPartitionSum N M c
  let B := Matrix.trace
    (sixVertexSectorTransfer (N + N) ((N + N) / 2) c ^ (M + M))
  let A := (2 : Real) ^ (4 * (N + M))
  have hZ : 0 < Z := sixVertexFixedWidthPartitionSum_pos N M hM hc
  have hB : 0 < B := by
    dsimp [B]
    exact sixVertexSector_trace_pow_pos (Nat.div_le_self (N + N) 2) hc _
  have hA : 0 < A := by positivity
  have hpow :=
    sixVertexFullTrace_pow_four_le_boundary_mul_doubledCentralTrace
      N M hN hM hNeven hMeven hc.le
  change Z ^ 4 <= A * B at hpow
  have hlog := Real.log_le_log (pow_pos hZ 4) hpow
  rw [Real.log_pow, Real.log_mul hA.ne' hB.ne', Real.log_pow] at hlog
  norm_num at hlog
  simpa [Z, B, Nat.cast_mul, Nat.cast_add, mul_add] using hlog



theorem sixVertexLogWidthTop_le_log_two_add_half_doubledCentral
    (N : Nat) (hN : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 0 < c) :
    Real.log (sixVertexWidthTopEigenvalue N c) <= Real.log 2 +
      Real.log (sixVertexSectorTopEigenvalue
        (N + N) ((N + N) / 2) (Nat.div_le_self (N + N) 2) c) / 2 := by
  let H : Nat -> Nat := fun m => 2 * (m + 1)
  let left : Nat -> Real := fun m =>
    4 * Real.log (sixVertexFixedWidthPartitionSum N (H m) c) / (H m : Real)
  let right : Nat -> Real := fun m =>
    ((4 * (N + H m) : Nat) : Real) * Real.log 2 / (H m : Real) +
      Real.log (Matrix.trace
        (sixVertexSectorTransfer (N + N) ((N + N) / 2) c ^
          (H m + H m))) / (H m : Real)
  have hH : Tendsto H atTop atTop := by
    refine tendsto_atTop.2 (fun K => ?_)
    filter_upwards [eventually_ge_atTop K] with m hm
    dsimp [H]
    omega
  have hHreal : Tendsto (fun m => (H m : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hH
  have hleft : Tendsto left atTop
      (nhds (4 * Real.log (sixVertexWidthTopEigenvalue N c))) := by
    have h :=
      (sixVertexFixedWidth_log_partition_div_height_tendsto N hc).comp hH
    have hmul : Tendsto (fun m =>
        4 * (Real.log (sixVertexFixedWidthPartitionSum N (H m) c) /
          (H m : Real))) atTop
        (nhds (4 * Real.log (sixVertexWidthTopEigenvalue N c))) :=
      tendsto_const_nhds.mul h
    apply hmul.congr'
    filter_upwards [] with m
    dsimp [left]
    ring
  have hdoubleH : Tendsto (fun m => H m + H m) atTop atTop := by
    refine tendsto_atTop.2 (fun K => ?_)
    filter_upwards [hH.eventually (eventually_ge_atTop K)] with m hm
    omega
  have hcentral0 :=
    (sixVertexSector_log_trace_div_height_tendsto_log_top
      (Nat.div_le_self (N + N) 2) hc).comp hdoubleH
  have hcentral : Tendsto (fun m =>
      Real.log (Matrix.trace
        (sixVertexSectorTransfer (N + N) ((N + N) / 2) c ^
          (H m + H m))) / (H m : Real)) atTop
      (nhds (2 * Real.log (sixVertexSectorTopEigenvalue
        (N + N) ((N + N) / 2) (Nat.div_le_self (N + N) 2) c))) := by
    have hmul : Tendsto (fun m =>
        2 * (Real.log (Matrix.trace
          (sixVertexSectorTransfer (N + N) ((N + N) / 2) c ^
            (H m + H m))) / ((H m + H m : Nat) : Real))) atTop
        (nhds (2 * Real.log (sixVertexSectorTopEigenvalue
          (N + N) ((N + N) / 2) (Nat.div_le_self (N + N) 2) c))) :=
      tendsto_const_nhds.mul hcentral0
    apply hmul.congr'
    filter_upwards [] with m
    have hHpos : (0 : Real) < H m := by
      exact_mod_cast (by dsimp [H]; omega : 0 < H m)
    push_cast
    field_simp [hHpos.ne']
    ring
  have hboundary : Tendsto (fun m =>
      ((4 * (N + H m) : Nat) : Real) * Real.log 2 / (H m : Real))
      atTop (nhds (4 * Real.log 2)) := by
    have hzero : Tendsto (fun m =>
        (((4 * N : Nat) : Real) * Real.log 2) / (H m : Real))
        atTop (nhds 0) :=
      hHreal.const_div_atTop (((4 * N : Nat) : Real) * Real.log 2)
    have hadd : Tendsto (fun m =>
        (((4 * N : Nat) : Real) * Real.log 2) / (H m : Real) +
          4 * Real.log 2) atTop (nhds (0 + 4 * Real.log 2)) :=
      hzero.add tendsto_const_nhds
    simpa only [zero_add] using hadd.congr' (by
      filter_upwards [] with m
      have hHpos : (0 : Real) < H m := by
        exact_mod_cast (by dsimp [H]; omega : 0 < H m)
      push_cast
      field_simp)
  have hright : Tendsto right atTop (nhds
      (4 * Real.log 2 + 2 * Real.log (sixVertexSectorTopEigenvalue
        (N + N) ((N + N) / 2) (Nat.div_le_self (N + N) 2) c))) := by
    simpa [right] using hboundary.add hcentral
  have hpoint : forall m, left m <= right m := by
    intro m
    have hHpos : 0 < H m := by dsimp [H]; omega
    have hHeven : Even (H m) := by
      exact ⟨m + 1, by dsimp [H]; omega⟩
    have hlog :=
      four_mul_log_sixVertexFullTrace_le_boundary_add_log_doubledCentral
        N (H m) hN hHpos hNeven hHeven hc
    dsimp [left, right]
    have hdiv := div_le_div_of_nonneg_right hlog
      (by positivity : (0 : Real) <= H m)
    convert hdiv using 1 <;> ring
  have hlimit := le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall hpoint)
  linarith



noncomputable def sixVertexFullWidthRate (c : Real) (k : Nat) : Real :=
  Real.log (sixVertexWidthTopEigenvalue (sixVertexFourWidth 0 k) c) /
    (sixVertexFourWidth 0 k : Real)


noncomputable def sixVertexFullAreaDensity (c : Real) (k M : Nat) : Real :=
  Real.log (sixVertexFixedWidthPartitionSum
    (sixVertexFourWidth 0 k) M c) /
      ((sixVertexFourWidth 0 k : Real) * (M : Real))



theorem sixVertexCentralWidthRate_le_fullWidthRate
    {c : Real} (hc : 0 < c) (k : Nat) :
    sixVertexCentralWidthRate c k <= sixVertexFullWidthRate c k := by
  let N := sixVertexFourWidth 0 k
  let middle : Fin (N + 1) := ⟨N / 2, by omega⟩
  have hsector := sixVertexWidthSectorTopEigenvalue_le N c middle
  have hsectorPos : 0 < sixVertexWidthSectorTopEigenvalue N c middle := by
    exact sixVertexSectorTopEigenvalue_pos
      (sixVertexWidthSectorIndex_le N middle) hc
  have hlog := Real.log_le_log hsectorPos hsector
  have hdiv := div_le_div_of_nonneg_right hlog
    (by positivity : (0 : Real) <= N)
  simpa [sixVertexCentralWidthRate, sixVertexLambdaAlongFour,
    sixVertexLambda, sixVertexFullWidthRate, N, middle,
    sixVertexWidthSectorTopEigenvalue] using hdiv



theorem sixVertexFullWidthRate_le_log_two_div_add_doubledCentral
    {c : Real} (hc : 0 < c) (k : Nat) :
    sixVertexFullWidthRate c k <=
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexCentralWidthRate c (2 * k + 1) := by
  let N := sixVertexFourWidth 0 k
  have h := sixVertexLogWidthTop_le_log_two_add_half_doubledCentral
    N (sixVertexFourWidth_pos 0 k) (sixVertexFourWidth_even 0 k) hc
  have hdiv := div_le_div_of_nonneg_right h
    (by positivity : (0 : Real) <= N)
  have hdouble : sixVertexFourWidth 0 (2 * k + 1) = N + N := by
    dsimp [N, sixVertexFourWidth]
    omega
  unfold sixVertexFullWidthRate sixVertexCentralWidthRate
  rw [sixVertexLambdaAlongFour, sixVertexLambda, hdouble]
  dsimp [N] at hdiv ⊢
  convert hdiv using 1 <;>
    push_cast <;>
    field_simp [Nat.cast_ne_zero.mpr (sixVertexFourWidth_pos 0 k).ne'] <;>
    ring




theorem tendsto_sixVertexFullWidthRate_canonicalPerron
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexFullWidthRate c) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) := by
  let a := sixVertexAntiferroelectricFreeEnergyValue
    (sixVertexAntiferroelectricLambda c)
  have hcentral : Tendsto (sixVertexCentralWidthRate c) atTop (nhds a) :=
    tendsto_sixVertexCentralWidthRate_canonicalPerron hc
  have hindex : Tendsto (fun k : Nat => 2 * k + 1) atTop atTop := by
    refine tendsto_atTop.2 (fun K => ?_)
    filter_upwards [eventually_ge_atTop K] with k hk
    omega
  have hcentralDouble : Tendsto (fun k =>
      sixVertexCentralWidthRate c (2 * k + 1)) atTop (nhds a) := by
    simpa only [Function.comp_apply] using hcentral.comp hindex
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    refine tendsto_atTop.2 (fun K => ?_)
    filter_upwards [eventually_ge_atTop K] with k hk
    unfold sixVertexFourWidth
    omega
  have hwidthReal : Tendsto (fun k =>
      (sixVertexFourWidth 0 k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidth
  have hboundary : Tendsto (fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) :=
    hwidthReal.const_div_atTop (Real.log 2)
  have hupper : Tendsto (fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexCentralWidthRate c (2 * k + 1)) atTop (nhds a) := by
    simpa only [zero_add] using hboundary.add hcentralDouble
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcentral hupper
  · exact Filter.Eventually.of_forall
      (sixVertexCentralWidthRate_le_fullWidthRate (by linarith))
  · exact Filter.Eventually.of_forall
      (sixVertexFullWidthRate_le_log_two_div_add_doubledCentral
        (by linarith))



theorem sixVertexFullAreaDensity_tendsto_widthRate
    {c : Real} (hc : 0 < c) (k : Nat) :
    Tendsto (sixVertexFullAreaDensity c k) atTop
      (nhds (sixVertexFullWidthRate c k)) := by
  let N := sixVertexFourWidth 0 k
  have h := sixVertexFixedWidth_log_partition_div_height_tendsto N hc
  have hdiv := h.div_const (N : Real)
  have hdiv' : Tendsto (fun M : Nat =>
      Real.log (sixVertexFixedWidthPartitionSum N M c) / (M : Real) /
        (N : Real)) atTop (nhds (sixVertexFullWidthRate c k)) := by
    simpa [sixVertexFullWidthRate, N] using hdiv
  apply hdiv'.congr'
  filter_upwards [eventually_gt_atTop (0 : Nat)] with M hM
  unfold sixVertexFullAreaDensity
  dsimp [N]
  field_simp




theorem sixVertexFull_iteratedLimit_of_canonicalPerron
    {c : Real} (hc : 2 < c) :
    SixVertexHasIteratedLimit (sixVertexFullAreaDensity c)
      (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c)) :=
  ⟨sixVertexFullWidthRate c,
    sixVertexFullAreaDensity_tendsto_widthRate (by linarith),
    tendsto_sixVertexFullWidthRate_canonicalPerron hc⟩




theorem fkQgt4_sixVertexFull_iteratedLimit
    {q : Real} (hq : 4 < q) :
    SixVertexHasIteratedLimit
      (sixVertexFullAreaDensity (fkQgt4SixVertexWeight q))
      (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))) :=
  sixVertexFull_iteratedLimit_of_canonicalPerron
    (two_lt_fkQgt4SixVertexWeight hq)

end

end StatMech.FrontierD
