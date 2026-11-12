/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectEulerNetNormalization
import Code.FrontierD.SixVertexBalancedBoundaryGluing
import Code.FrontierD.SixVertexBlockRepetition

open Filter Topology

namespace StatMech.FrontierD

noncomputable section



def sixVertexDoubledBalancedShare (N M : Nat) (c : Real) : Real :=
  sixVertexRectangleBalancedPartitionSum (N + N) (M + M) c /
    sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c



theorem sixVertexDoubledBalancedShare_lower
    {N M : Nat} (hN : 0 < N) (hM : 0 < M)
    {c : Real} (hc : 0 <= c) :
    sixVertexRectangleToroidalPartitionSum N M c ^ 4 /
          ((2 : Real) ^ (4 * (N + M)) *
            sixVertexRectangleToroidalPartitionSum
              (N + N) (M + M) c) <=
      sixVertexDoubledBalancedShare N M c := by
  let Z := sixVertexRectangleToroidalPartitionSum N M c
  let K := sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c
  let B := sixVertexRectangleBalancedPartitionSum (N + N) (M + M) c
  let Z2 := sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c
  have hZ : 0 <= Z :=
    sixVertexRectangleToroidalPartitionSum_nonneg N M hc
  have hZK : Z <= (2 : Real) ^ (N + M) * K :=
    sixVertexRectangleToroidalPartitionSum_le_card_mul_maxBoundary N M c
  have hK : K ^ 4 <= B :=
    sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubledBalanced
      hN hM hc
  have hpow : Z ^ 4 <= (2 : Real) ^ (4 * (N + M)) * B := by
    calc
      Z ^ 4 <= ((2 : Real) ^ (N + M) * K) ^ 4 :=
        pow_le_pow_left₀ hZ hZK 4
      _ = ((2 : Real) ^ (N + M)) ^ 4 * K ^ 4 := by rw [mul_pow]
      _ <= ((2 : Real) ^ (N + M)) ^ 4 * B :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      _ = (2 : Real) ^ (4 * (N + M)) * B := by
        rw [← pow_mul]
        congr 2
        omega
  have hZ2 : 0 < Z2 := by
    have hsub := sixVertexRectangleBalancedPartitionSum_le_toroidal
      (N + N) (M + M) hc
    exact (sixVertexRectangleBalancedPartitionSum_pos
      (N + N) (M + M) hc).trans_le hsub
  unfold sixVertexDoubledBalancedShare
  dsimp only [Z, B, Z2] at hpow hZ2 ⊢
  have hboundary : 0 < (2 : Real) ^ (4 * (N + M)) := by positivity
  rw [div_le_iff₀ (mul_pos hboundary hZ2)]
  calc
    sixVertexRectangleToroidalPartitionSum N M c ^ 4 <=
        (2 : Real) ^ (4 * (N + M)) *
          sixVertexRectangleBalancedPartitionSum (N + N) (M + M) c := hpow
    _ = (sixVertexRectangleBalancedPartitionSum (N + N) (M + M) c /
          sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c) *
        ((2 : Real) ^ (4 * (N + M)) *
          sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c) := by
      field_simp



theorem sixVertexDoubledBalancedShare_negLog_le
    {N M : Nat} (hN : 0 < N) (hM : 0 < M)
    {c : Real} (hc : 0 <= c) :
    -Real.log (sixVertexDoubledBalancedShare N M c) <=
      Real.log
          (sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c) -
        4 * Real.log (sixVertexRectangleToroidalPartitionSum N M c) +
        (4 * (N + M) : Nat) * Real.log 2 := by
  let Z := sixVertexRectangleToroidalPartitionSum N M c
  let Z2 := sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c
  let A := (2 : Real) ^ (4 * (N + M))
  have hZ : 0 < Z := by
    exact (sixVertexRectangleBalancedPartitionSum_pos N M hc).trans_le
      (sixVertexRectangleBalancedPartitionSum_le_toroidal N M hc)
  have hZ2 : 0 < Z2 := by
    exact (sixVertexRectangleBalancedPartitionSum_pos
      (N + N) (M + M) hc).trans_le
      (sixVertexRectangleBalancedPartitionSum_le_toroidal
        (N + N) (M + M) hc)
  have hA : 0 < A := by positivity
  have hlower := sixVertexDoubledBalancedShare_lower hN hM hc
  have hleft : 0 < Z ^ 4 / (A * Z2) := by positivity
  have hlog := Real.log_le_log hleft hlower
  change Real.log (Z ^ 4 / (A * Z2)) <=
    Real.log (sixVertexDoubledBalancedShare N M c) at hlog
  rw [Real.log_div (pow_ne_zero 4 hZ.ne')
      (mul_ne_zero hA.ne' hZ2.ne'),
    Real.log_pow, Real.log_mul hA.ne' hZ2.ne', Real.log_pow] at hlog
  dsimp only [A, Z, Z2] at hlog ⊢
  norm_num at hlog ⊢
  linarith



theorem fkRectBalancedSectorShare_eq_doubledBalancedShare
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorShare R q =
      sixVertexDoubledBalancedShare R.width (R.height / 2)
        (fkQgt4SixVertexWeight q) := by
  rw [fkRectBalancedSectorShare_eq_sixVertexRatio R hq,
    sixVertexTorusFixedCharge_zero_eq_balanced,
    ← sixVertexRectangleBalancedPartitionSum_eq_torusBalancedArrow,
    ← sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum]
  change
    sixVertexRectangleBalancedPartitionSum (2 * R.width) R.height
          (fkQgt4SixVertexWeight q) /
        sixVertexRectangleToroidalPartitionSum (2 * R.width) R.height
          (fkQgt4SixVertexWeight q) = _
  unfold sixVertexDoubledBalancedShare
  have hh : R.height / 2 + R.height / 2 = R.height := by
    obtain ⟨k, hk⟩ := R.height_even
    omega
  rw [hh]
  congr 3 <;> omega


theorem fkRectBalancedSectorShare_lower_of_fourCopy
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    sixVertexRectangleToroidalPartitionSum R.width (R.height / 2)
          (fkQgt4SixVertexWeight q) ^ 4 /
        ((2 : Real) ^ (4 * (R.width + R.height / 2)) *
          sixVertexRectangleToroidalPartitionSum
            (R.width + R.width)
            (R.height / 2 + R.height / 2)
            (fkQgt4SixVertexWeight q)) <=
      fkRectBalancedSectorShare R q := by
  rw [fkRectBalancedSectorShare_eq_doubledBalancedShare R hq]
  apply sixVertexDoubledBalancedShare_lower R.width_pos
  · exact Nat.div_pos (Nat.le_of_lt R.height_gt_two) (by norm_num)
  · exact (lt_trans (by norm_num : (0 : Real) < 2)
      (two_lt_fkQgt4SixVertexWeight hq)).le


theorem fkRectBalancedSectorShare_negLog_le_fourCopy
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    -Real.log (fkRectBalancedSectorShare R q) <=
      Real.log (sixVertexRectangleToroidalPartitionSum
          (R.width + R.width) (R.height / 2 + R.height / 2)
          (fkQgt4SixVertexWeight q)) -
        4 * Real.log (sixVertexRectangleToroidalPartitionSum
          R.width (R.height / 2) (fkQgt4SixVertexWeight q)) +
        (4 * (R.width + R.height / 2) : Nat) * Real.log 2 := by
  rw [fkRectBalancedSectorShare_eq_doubledBalancedShare R hq]
  apply sixVertexDoubledBalancedShare_negLog_le R.width_pos
  · exact Nat.div_pos (Nat.le_of_lt R.height_gt_two) (by norm_num)
  · exact (lt_trans (by norm_num : (0 : Real) < 2)
      (two_lt_fkQgt4SixVertexWeight hq)).le



theorem fkRectBalancedNormalization_negLog_le_all_add_fourCopy
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    -Real.log (fkRectBalancedSectorNormalization R q) <=
      -Real.log (fkRectAllSectorNormalization R q) +
        (Real.log (sixVertexRectangleToroidalPartitionSum
            (R.width + R.width) (R.height / 2 + R.height / 2)
            (fkQgt4SixVertexWeight q)) -
          4 * Real.log (sixVertexRectangleToroidalPartitionSum
            R.width (R.height / 2) (fkQgt4SixVertexWeight q)) +
          (4 * (R.width + R.height / 2) : Nat) * Real.log 2) := by
  rw [balancedNormalization_negLog_eq_all_add_share R hq]
  have h := fkRectBalancedSectorShare_negLog_le_fourCopy R hq
  linarith


def fkRectFourCopyShareCost (R : FKRectTorus) (q : Real) : Real :=
  Real.log (sixVertexRectangleToroidalPartitionSum
      (R.width + R.width) (R.height / 2 + R.height / 2)
      (fkQgt4SixVertexWeight q)) -
    4 * Real.log (sixVertexRectangleToroidalPartitionSum
      R.width (R.height / 2) (fkQgt4SixVertexWeight q)) +
    (4 * (R.width + R.height / 2) : Nat) * Real.log 2

theorem fkRectBalancedSectorShare_negLog_le_fourCopyCost
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    -Real.log (fkRectBalancedSectorShare R q) <=
      fkRectFourCopyShareCost R q := by
  exact fkRectBalancedSectorShare_negLog_le_fourCopy R hq



theorem tendsto_balancedShare_negLog_div_height_zero_of_fourCopyCost
    (R : Nat -> FKRectTorus) {q : Real} (hq : 4 < q)
    (hcost : Tendsto (fun n =>
      fkRectFourCopyShareCost (R n) q / (R n).height)
        atTop (nhds 0)) :
    Tendsto (fun n =>
      -Real.log (fkRectBalancedSectorShare (R n) q) / (R n).height)
        atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n =>
      -Real.log (fkRectBalancedSectorShare (R n) q) / (R n).height)
    tendsto_const_nhds hcost
  · filter_upwards [] with n
    apply div_nonneg
    · rw [neg_nonneg]
      exact Real.log_nonpos
        (fkRectBalancedSectorShare_mem_Ioc (R n) hq).1.le
        (fkRectBalancedSectorShare_mem_Ioc (R n) hq).2
    · positivity
  · filter_upwards [] with n
    apply div_le_div_of_nonneg_right
      (fkRectBalancedSectorShare_negLog_le_fourCopyCost (R n) hq)
    positivity




theorem tendsto_balancedNormalization_negLog_div_height_zero_of_all_and_fourCopy
    (R : Nat -> FKRectTorus) {q : Real} (hq : 4 < q)
    (hall : Tendsto (fun n =>
      -Real.log (fkRectAllSectorNormalization (R n) q) / (R n).height)
        atTop (nhds 0))
    (hcost : Tendsto (fun n =>
      fkRectFourCopyShareCost (R n) q / (R n).height)
        atTop (nhds 0)) :
    Tendsto (fun n =>
      -Real.log (fkRectBalancedSectorNormalization (R n) q) /
        (R n).height) atTop (nhds 0) := by
  have hshare :=
    tendsto_balancedShare_negLog_div_height_zero_of_fourCopyCost R hq hcost
  have hadd := hall.add hshare
  have htarget : Tendsto (fun n =>
      -Real.log (fkRectBalancedSectorNormalization (R n) q) /
        (R n).height) atTop (nhds (0 + 0)) := by
    apply hadd.congr'
    filter_upwards [] with n
    rw [balancedNormalization_negLog_eq_all_add_share (R n) hq]
    ring
  simpa using htarget

end

end StatMech.FrontierD
