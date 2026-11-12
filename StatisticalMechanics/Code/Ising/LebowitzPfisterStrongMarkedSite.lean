/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamMarkedSiteCorollary











open scoped BigOperators
open Finset Filter Set

set_option linter.unusedSectionVars false

namespace StatMech.Ising

open StatMech.Sharpness StatMech.FrontierA

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2400000 in


theorem grahamMarkedSite_strong_with_parameter
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hK : forall e, 0 <= K e)
    (i j k l : V)
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * grahamTwoPoint G.edgeFinset K k l *
        (grahamTwoPoint G.edgeFinset K i k -
          q ^ 2 * grahamTwoPoint G.edgeFinset K i l *
            grahamTwoPoint G.edgeFinset K k l) *
        (grahamTwoPoint G.edgeFinset K j k -
          q ^ 2 * grahamTwoPoint G.edgeFinset K j l *
            grahamTwoPoint G.edgeFinset K k l) <=
      (1 - q ^ 2 * grahamTwoPoint G.edgeFinset K k l ^ 2) *
        (-(grahamUrsell4 G.edgeFinset K i j k l +
          2 * q ^ 2 *
            (grahamTwoPoint G.edgeFinset K i l *
              grahamTwoPoint G.edgeFinset K j l *
              grahamTwoPoint G.edgeFinset K k l))) := by
  let t := Real.artanh q
  have hqmem : q ∈ Ioo (-1 : Real) 1 := by
    exact And.intro (by linarith) hq1
  have ht : Real.tanh t = q := Real.tanh_artanh hqmem
  have hfield : forall x, 0 <= lebowitzPointField l t x := by
    intro x
    by_cases hx : x = l
    · simp [lebowitzPointField, hx, t, Real.artanh_nonneg, hq0.le]
    · simp [lebowitzPointField, hx]
  have hstrong := grahamImprovedGHS_inhomogeneous_strong G K
    (lebowitzPointField l t) hK hfield i j k
  unfold ghsiUrsell3 ghsiCovariance grahamInhomOne at hstrong
  rw [expJ_pointField_three_eq_all G.edgeFinset K i j k l,
    expJ_pointField_one_eq G.edgeFinset K i l,
    expJ_pointField_two_eq_all G.edgeFinset K j k l,
    expJ_pointField_two_eq_all G.edgeFinset K i j l,
    expJ_pointField_one_eq G.edgeFinset K k l,
    expJ_pointField_two_eq_all G.edgeFinset K i k l,
    expJ_pointField_one_eq G.edgeFinset K j l,
    ht] at hstrong
  rw [grahamUrsell4_eq_expJ]
  simp only [grahamTwoPoint_eq_expJ]
  nlinarith [hstrong]

set_option maxHeartbeats 2400000 in





theorem grahamMarkedSite_four_point_strong
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hK : forall e, 0 <= K e)
    (i j k l : V) :
    2 * grahamTwoPoint G.edgeFinset K k l *
        grahamBridgeGap G.edgeFinset K i k l *
        grahamBridgeGap G.edgeFinset K j k l <=
      (1 - grahamTwoPoint G.edgeFinset K k l ^ 2) *
        (-(grahamUrsell4 G.edgeFinset K i j k l +
          2 * (grahamTwoPoint G.edgeFinset K i l *
            grahamTwoPoint G.edgeFinset K j l *
            grahamTwoPoint G.edgeFinset K k l))) := by
  let P := grahamTwoPoint G.edgeFinset K i l *
    grahamTwoPoint G.edgeFinset K j l *
    grahamTwoPoint G.edgeFinset K k l
  let A := grahamTwoPoint G.edgeFinset K i k
  let B := grahamTwoPoint G.edgeFinset K i l *
    grahamTwoPoint G.edgeFinset K k l
  let C := grahamTwoPoint G.edgeFinset K j k
  let D := grahamTwoPoint G.edgeFinset K j l *
    grahamTwoPoint G.edgeFinset K k l
  let L := grahamTwoPoint G.edgeFinset K k l
  let U := grahamUrsell4 G.edgeFinset K i j k l
  let q : Nat -> Real := fun n => 1 - 1 / (n + 1 : Real)
  have hq0 : forall n : Nat, 0 < q (n + 1) := by
    intro n
    dsimp [q]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hden : (0 : Real) < ((n : Real) + 1) + 1 := by positivity
    have hlt : (1 : Real) / (((n : Real) + 1) + 1) < 1 :=
      (div_lt_one hden).2 (by
        nlinarith [show (0 : Real) <= n from Nat.cast_nonneg n])
    linarith
  have hq1 : forall n : Nat, q (n + 1) < 1 := by
    intro n
    dsimp [q]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hden : (0 : Real) < ((n : Real) + 1) + 1 := by positivity
    have hpos : (0 : Real) < 1 / (((n : Real) + 1) + 1) :=
      div_pos zero_lt_one hden
    linarith
  have hineq : forall n : Nat,
      2 * L * (A - (q (n + 1)) ^ 2 * B) *
          (C - (q (n + 1)) ^ 2 * D) <=
        (1 - (q (n + 1)) ^ 2 * L ^ 2) *
          (-(U + 2 * (q (n + 1)) ^ 2 * P)) := by
    intro n
    convert grahamMarkedSite_strong_with_parameter G K hK i j k l
      (q (n + 1)) (hq0 n) (hq1 n) using 1
    all_goals
      simp only [A, B, C, D, L]
      ring_nf
  have hq_tendsto : Tendsto (fun n : Nat => q (n + 1)) atTop (nhds 1) := by
    have hzero' := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    have hzero : Tendsto (fun n : Nat => (1 : Real) / (n + 1 + 1 : Real))
        atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hzero'
    simpa [q, Nat.cast_add, Nat.cast_one] using tendsto_const_nhds.sub hzero
  have hleft : Tendsto (fun n : Nat =>
      2 * L * (A - (q (n + 1)) ^ 2 * B) *
        (C - (q (n + 1)) ^ 2 * D)) atTop
      (nhds (2 * L * (A - B) * (C - D))) := by
    convert (((tendsto_const_nhds.mul tendsto_const_nhds).mul
      (tendsto_const_nhds.sub
        ((hq_tendsto.pow 2).mul tendsto_const_nhds))).mul
      (tendsto_const_nhds.sub
        ((hq_tendsto.pow 2).mul tendsto_const_nhds))) using 1
    all_goals ring_nf
  have hright : Tendsto (fun n : Nat =>
      (1 - (q (n + 1)) ^ 2 * L ^ 2) *
        (-(U + 2 * (q (n + 1)) ^ 2 * P))) atTop
      (nhds ((1 - L ^ 2) * (-(U + 2 * P)))) := by
    convert ((tendsto_const_nhds.sub
      ((hq_tendsto.pow 2).mul tendsto_const_nhds)).mul
      (tendsto_const_nhds.add
        ((tendsto_const_nhds.mul (hq_tendsto.pow 2)).mul
          tendsto_const_nhds)).neg) using 1
    all_goals ring_nf
  have hlimit : 2 * L * (A - B) * (C - D) <=
      (1 - L ^ 2) * (-(U + 2 * P)) :=
    le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hineq)
  simpa [P, A, B, C, D, L, U, grahamBridgeGap,
    grahamTwoPoint_comm G.edgeFinset K l k] using hlimit


theorem grahamMarkedSite_four_point_strong_edgeFinset
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : forall e, 0 <= J e)
    (i j k l : V) :
    2 * grahamTwoPoint E J k l * grahamBridgeGap E J i k l *
        grahamBridgeGap E J j k l <=
      (1 - grahamTwoPoint E J k l ^ 2) *
        (-(grahamUrsell4 E J i j k l +
          2 * (grahamTwoPoint E J i l * grahamTwoPoint E J j l *
            grahamTwoPoint E J k l))) := by
  have h := grahamMarkedSite_four_point_strong
    (grahamGraph E) J hJ i j k l
  rw [grahamGraph_edgeFinset E hdiag] at h
  exact h

end

end StatMech.Ising
