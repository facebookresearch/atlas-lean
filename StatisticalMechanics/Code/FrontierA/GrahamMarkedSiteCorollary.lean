/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Ising.LebowitzFourPoint
import Code.FrontierA.GrahamHeadlineAdapter
import Code.FrontierA.GrahamGraphAdapter

open scoped BigOperators
open Finset Filter Set

set_option linter.unusedSectionVars false

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem expJ_zero_three_spin_eq_zero_all
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (x y z : V) :
    expJ E J (fun _ => 0)
      (fun s => spin s x * (spin s y * spin s z)) = 0 := by
  by_cases hxy : x = y
  · subst y
    rw [show (fun s : ConfigSpace V => spin s x * (spin s x * spin s z)) =
        (fun s => spin s z) by
      funext s
      rw [← mul_assoc, spin_sq, one_mul],
      expJ_zero_spin_eq_zero]
  · by_cases hxz : x = z
    · subst z
      rw [show (fun s : ConfigSpace V => spin s x * (spin s y * spin s x)) =
          (fun s => spin s y) by
        funext s
        calc
          spin s x * (spin s y * spin s x) =
              spin s y * (spin s x * spin s x) := by ring
          _ = spin s y := by rw [spin_sq, mul_one],
        expJ_zero_spin_eq_zero]
    · by_cases hyz : y = z
      · subst z
        rw [show (fun s : ConfigSpace V => spin s x * (spin s y * spin s y)) =
            (fun s => spin s x) by
          funext s
          rw [spin_sq, mul_one],
          expJ_zero_spin_eq_zero]
      · exact expJ_zero_three_spin_eq_zero E J x y z hxy hxz hyz



theorem expJ_pointField_two_eq_all
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (x y l : V) (t : Real) :
    expJ E J (lebowitzPointField l t)
        (fun s => spin s x * spin s y) =
      expJ E J (fun _ => 0) (fun s => spin s x * spin s y) := by
  rw [expJ_pointField_eq]
  have hodd := expJ_zero_three_spin_eq_zero_all E J x y l
  rw [show (fun s : ConfigSpace V =>
      (spin s x * spin s y) * spin s l) =
      (fun s => spin s x * (spin s y * spin s l)) by
        funext s
        ring,
    hodd, mul_zero, add_zero]



theorem expJ_pointField_three_eq_all
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (i j k l : V) (t : Real) :
    expJ E J (lebowitzPointField l t)
        (fun s => spin s i * (spin s j * spin s k)) =
      Real.tanh t * expJ E J (fun _ => 0)
        (fun s => (spin s i * spin s j) * (spin s k * spin s l)) := by
  rw [expJ_pointField_eq, expJ_zero_three_spin_eq_zero_all, zero_add]
  congr 2
  funext s
  ring

set_option maxHeartbeats 2400000 in



theorem grahamMarkedSite_with_parameter
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hK : forall e, 0 <= K e)
    (i j k l : V)
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) :
    grahamUrsell4 G.edgeFinset K i j k l +
        2 * q ^ 2 *
          (grahamTwoPoint G.edgeFinset K i l *
            grahamTwoPoint G.edgeFinset K j l *
            grahamTwoPoint G.edgeFinset K k l) <=
      -2 *
        (grahamTwoPoint G.edgeFinset K i k -
          q ^ 2 * grahamTwoPoint G.edgeFinset K i l *
            grahamTwoPoint G.edgeFinset K k l) *
        (grahamTwoPoint G.edgeFinset K j k -
          q ^ 2 * grahamTwoPoint G.edgeFinset K j l *
            grahamTwoPoint G.edgeFinset K k l) *
        grahamTwoPoint G.edgeFinset K k l := by
  let t := Real.artanh q
  have hqmem : q ∈ Set.Ioo (-1 : Real) 1 := by
    exact And.intro (by linarith) hq1
  have ht : Real.tanh t = q := Real.tanh_artanh hqmem
  have hfield : forall x, 0 <= lebowitzPointField l t x := by
    intro x
    by_cases hx : x = l
    · simp [lebowitzPointField, hx, t, Real.artanh_nonneg, hq0.le]
    · simp [lebowitzPointField, hx]
  have hghs := grahamImprovedGHS_inhomogeneous G K
    (lebowitzPointField l t) hK hfield i j k
  unfold ghsiUrsell3 ghsiCovariance grahamInhomOne at hghs
  rw [expJ_pointField_three_eq_all G.edgeFinset K i j k l,
    expJ_pointField_one_eq G.edgeFinset K i l,
    expJ_pointField_two_eq_all G.edgeFinset K j k l,
    expJ_pointField_two_eq_all G.edgeFinset K i j l,
    expJ_pointField_one_eq G.edgeFinset K k l,
    expJ_pointField_two_eq_all G.edgeFinset K i k l,
    expJ_pointField_one_eq G.edgeFinset K j l,
    ht] at hghs
  rw [grahamUrsell4_eq_expJ]
  simp only [grahamTwoPoint_eq_expJ]
  nlinarith [hghs]

set_option maxHeartbeats 2400000 in



theorem grahamMarkedSite_four_point
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hK : forall e, 0 <= K e)
    (i j k l : V) :
    grahamUrsell4 G.edgeFinset K i j k l <=
      grahamCorrectedRHS G.edgeFinset K i j k l l := by
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
      grahamUrsell4 G.edgeFinset K i j k l +
          2 * (q (n + 1)) ^ 2 * P <=
        -2 * (A - (q (n + 1)) ^ 2 * B) *
          (C - (q (n + 1)) ^ 2 * D) * L := by
    intro n
    convert grahamMarkedSite_with_parameter G K hK i j k l
      (q (n + 1)) (hq0 n) (hq1 n) using 1
    all_goals (simp only [A, B, C, D, L]; ring_nf)
  have hq_tendsto : Tendsto (fun n : Nat => q (n + 1)) atTop (nhds 1) := by
    have hzero' := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    have hzero : Tendsto (fun n : Nat => (1 : Real) / (n + 1 + 1 : Real))
        atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hzero'
    simpa [q, Nat.cast_add, Nat.cast_one] using tendsto_const_nhds.sub hzero
  have hleft : Tendsto (fun n : Nat =>
      grahamUrsell4 G.edgeFinset K i j k l +
        2 * (q (n + 1)) ^ 2 * P) atTop
      (nhds (grahamUrsell4 G.edgeFinset K i j k l + 2 * P)) := by
    convert tendsto_const_nhds.add
      ((tendsto_const_nhds.mul (hq_tendsto.pow 2)).mul
        tendsto_const_nhds) using 1
    all_goals ring
  have hcorrection : Tendsto (fun n : Nat =>
      2 * (A - (q (n + 1)) ^ 2 * B) *
        (C - (q (n + 1)) ^ 2 * D) * L) atTop
      (nhds (2 * (A - B) * (C - D) * L)) := by
    convert (((tendsto_const_nhds.mul
      (tendsto_const_nhds.sub
        ((hq_tendsto.pow 2).mul tendsto_const_nhds))).mul
      (tendsto_const_nhds.sub
        ((hq_tendsto.pow 2).mul tendsto_const_nhds))).mul
      tendsto_const_nhds) using 1
    all_goals ring
  have hlim : Tendsto (fun n : Nat =>
      grahamUrsell4 G.edgeFinset K i j k l +
        2 * (q (n + 1)) ^ 2 * P +
        2 * (A - (q (n + 1)) ^ 2 * B) *
          (C - (q (n + 1)) ^ 2 * D) * L) atTop
      (nhds (grahamUrsell4 G.edgeFinset K i j k l + 2 * P +
        2 * (A - B) * (C - D) * L)) := by
    exact hleft.add hcorrection
  have hnonpos : forall n : Nat,
      grahamUrsell4 G.edgeFinset K i j k l +
        2 * (q (n + 1)) ^ 2 * P +
        2 * (A - (q (n + 1)) ^ 2 * B) *
          (C - (q (n + 1)) ^ 2 * D) * L <= 0 := by
    intro n
    linarith [hineq n]
  have hfinal := le_of_tendsto' hlim hnonpos
  rw [grahamCorrectedRHS_aux_eq_l]
  dsimp only [P, A, B, C, D, L] at hfinal
  unfold grahamBridgeGap
  rw [grahamTwoPoint_comm G.edgeFinset K l k]
  nlinarith


theorem grahamMarkedSite_four_point_edgeFinset
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : forall e, 0 <= J e)
    (i j k l : V) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l l := by
  have h := grahamMarkedSite_four_point (grahamGraph E) J hJ i j k l
  rw [grahamGraph_edgeFinset E hdiag] at h
  exact h

end

end StatMech.FrontierA
