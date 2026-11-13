/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCylinderTransverseTail
import Code.FrontierD.FKRectVerticalWindingPrimitiveCapstone
import Code.Probability.FiniteExponentialRateComparison










open Filter Topology

namespace StatMech.FrontierD

noncomputable section




theorem fkQgt4_sqrtExactDiagonal_heightSubOne_negLogRate_tendsto
    {q : Real} (hq : 4 < q) (R : Nat -> FKRectTorus)
    (hheight : Tendsto (fun n => (R n).height) atTop atTop) :
    Tendsto (fun n =>
      -Real.log (Real.sqrt
        (fkQgt4CriticalFreeExactDiagonalTwoPoint hq ((R n).height - 1))) /
          ((R n).height : Real)) atTop
      (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) := by
  let m : Nat -> Nat := fun n => (R n).height - 1
  have hm : Tendsto m atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hheight
  have hdiag :=
    (fkQgt4CriticalFreeExactDiagonalRate_tendsto hq).comp hm
  have hheightReal : Tendsto (fun n => ((R n).height : Real))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hheight
  have hinv : Tendsto (fun n => 1 / ((R n).height : Real))
      atTop (nhds 0) := hheightReal.const_div_atTop 1
  have hratio : Tendsto (fun n => (m n : Real) / ((R n).height : Real))
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hbase := hone.sub hinv
    have hbase' : Tendsto (fun n =>
        (1 : Real) - 1 / ((R n).height : Real)) atTop (nhds 1) := by
      simpa using hbase
    apply hbase'.congr'
    filter_upwards with n
    have hh := (R n).height_pos
    have hhReal : ((R n).height : Real) ≠ 0 := by positivity
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 <= (R n).height)]
    field_simp
    norm_num
  have hprod := hdiag.mul hratio
  have hhalf := hprod.const_mul (1 / 2 : Real)
  have hlimit : (1 / 2 : Real) *
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq * 1) =
        fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by ring
  rw [hlimit] at hhalf
  apply hhalf.congr'
  filter_upwards with n
  have hmPos : 0 < m n := by
    dsimp [m]
    have hh := (R n).height_gt_two
    omega
  have hmReal : (m n : Real) ≠ 0 := by positivity
  have hdiagNonneg : 0 <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (m n) :=
    (fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq (m n)).le
  rw [Real.log_sqrt hdiagNonneg]
  dsimp only [Function.comp_apply]
  field_simp



theorem fkQgt4_mul_pred_exactDiagonalHalf_le_windingTailRate
    {q tailRate : Real} (hq : 4 < q)
    (R : Nat -> FKRectTorus) (width r : Nat)
    (hr : 0 < r) (hrwidth : r <= width)
    (hwidth : forall n, (R n).width = width)
    (hheight : Tendsto (fun n => (R n).height) atTop atTop)
    (hcross : forall n,
      FKRectWindingTailForcesHorizontalCylinderCrossings (R n) r)
    (htailRate : Tendsto (fun n =>
      -Real.log (fkRectCriticalWindingTailMass (R n) q r) /
        ((R n).height : Real)) atTop (nhds tailRate)) :
    ((r - 1 : Nat) : Real) *
        (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
      tailRate := by
  let tail : Nat -> Real := fun n =>
    fkRectCriticalWindingTailMass (R n) q r
  let corr : Nat -> Real := fun n =>
    Real.sqrt
      (fkQgt4CriticalFreeExactDiagonalTwoPoint hq ((R n).height - 1))
  let a : Real := FK.cFE (fkRectCriticalP q) q ^ (2 * width)
  let b : Real := Nat.choose width r * width ^ width
  have hwidthPos : 0 < width := by
    rw [← hwidth 0]
    exact (R 0).width_pos
  have ha : 0 < a := by
    exact pow_pos (FK.cFE_pos
      (fkRectCriticalP_pos (by linarith : (0 : Real) < q))
      (fkRectCriticalP_lt_one (by linarith : (0 : Real) < q))
      (by linarith : (1 : Real) <= q)) _
  have hb : 0 < b := by
    dsimp [b]
    exact mul_pos
      (by exact_mod_cast Nat.choose_pos hrwidth)
      (by exact_mod_cast pow_pos hwidthPos width)
  have htail : forall n, 0 < tail n := by
    intro n
    apply fkRectCriticalWindingTailMass_pos_of_fixedCharge (R n) hq r
    simpa [FKRectTorus.medialTorus, hwidth n] using hrwidth
  have hcorr : forall n, 0 < corr n := by
    intro n
    exact Real.sqrt_pos.2
      (fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq ((R n).height - 1))
  have hheightPos : forall n, 0 < (R n).height := fun n => (R n).height_pos
  have hbound : forall n,
      a * tail n <= b * corr n ^ (r - 1) := by
    intro n
    have h :=
      fkRectCriticalWindingTailMass_cFE_le_crossingPrefactor_mul_sqrtExact
        hq (R n) r hr (hcross n)
    simpa [a, b, tail, corr, hwidth n] using h
  apply StatMech.Probability.pow_negLogRate_le_negLogRate_of_mul_le_mul_pow
    ha hb htail hcorr hheightPos hheight hbound
  · simpa [tail] using htailRate
  · simpa [corr] using
      fkQgt4_sqrtExactDiagonal_heightSubOne_negLogRate_tendsto hq R hheight



theorem fkQgt4_mul_pred_exactDiagonalHalf_le_windingTailRate_unconditional
    {q tailRate : Real} (hq : 4 < q)
    (R : Nat -> FKRectTorus) (width r : Nat)
    (hr : 0 < r) (hrwidth : r <= width)
    (hwidth : forall n, (R n).width = width)
    (hheight : Tendsto (fun n => (R n).height) atTop atTop)
    (htailRate : Tendsto (fun n =>
      -Real.log (fkRectCriticalWindingTailMass (R n) q r) /
        ((R n).height : Real)) atTop (nhds tailRate)) :
    ((r - 1 : Nat) : Real) *
        (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
      tailRate := by
  apply fkQgt4_mul_pred_exactDiagonalHalf_le_windingTailRate
    hq R width r hr hrwidth hwidth hheight
  · intro n
    exact fkRectWindingTailForcesHorizontalCylinderCrossings_unconditional
      (R n) r
  · exact htailRate

end

end StatMech.FrontierD
