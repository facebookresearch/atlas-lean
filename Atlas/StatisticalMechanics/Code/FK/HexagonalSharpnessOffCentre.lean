/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.HexagonalOffCentre
import Code.OSSS.WiredDenominatorArithmetic





open scoped BigOperators Classical
open Finset Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice
open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree
open StatMech.OSSS.FiniteGraphBoundaryDifferential
open StatMech.OSSS.ReachBoxCrossing
open StatMech.OSSS.RevealmentTranslation

noncomputable def hexagonalBoxCenteredShell
    (n : Nat) (x : HexagonalBoxVertex n) (k : Nat) :
    Finset (HexagonalBoxVertex n) :=
  Finset.univ.filter fun y => centeredRadius x.1.1 y.1.1 = k

noncomputable def hexagonalOuterCenteredConn
    (n : Nat) (q beta : Real) (x : HexagonalBoxVertex n) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      x (hexagonalBoxCenteredShell n x k) then (1 : Real) else 0)



theorem hexagonalBox_reachOpen_hits_centered
    {n m : Nat} {omega : ConfigSpace (hexagonalBoxGraph n).edgeSet}
    {x b : HexagonalBoxVertex n}
    (hreach : ReachOpen (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x b)
    (hm : m ≤ centeredRadius x.1.1 b.1.1) :
    ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x
      (hexagonalBoxCenteredShell n x m) := by
  by_cases hm0 : m = 0
  · subst m
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, centeredRadius_self x.1.1⟩,
      ReachOpen.refl x⟩
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hbOuter : b.1.1 - x.1.1 ∉ box 2 (m - 1) := by
    intro hb
    have hbRad : centeredRadius x.1.1 b.1.1 ≤ m - 1 := by
      rw [mem_box_iff_siteRadius_le] at hb
      simpa [centeredRadius, siteRadius, Pi.sub_apply] using hb
    omega
  have hxInner : x.1.1 - x.1.1 ∈ box 2 (m - 1) := by simp
  have hfirst : ∀ {a b : HexagonalBoxVertex n},
      ReachOpen (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega a b →
      a.1.1 - x.1.1 ∈ box 2 (m - 1) →
        b.1.1 - x.1.1 ∉ box 2 (m - 1) →
      ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega a
        (hexagonalBoxCenteredShell n x m) := by
    intro a b hr
    induction hr with
    | refl a => intro ha hnot; exact (hnot ha).elim
    | @step a y z e hopen hpair hrest ih =>
        intro ha hz
        have hay : (hexagonalBoxGraph n).Adj a y := by
          rcases hpair with hpair | hpair
          · rw [← hpair.1, ← hpair.2]
            exact hexagonalBox_end_adj n e
          · rw [← hpair.1, ← hpair.2]
            exact (hexagonalBox_end_adj n e).symm
        by_cases hy : y.1.1 - x.1.1 ∈ box 2 (m - 1)
        · obtain ⟨w, hw, hwy⟩ := ih hy hz
          exact ⟨w, hw, ReachOpen.step e hopen hpair hwy⟩
        · have hadjSub : hexagonalGraph.Adj
              (a.1.1 - x.1.1, a.1.2) (y.1.1 - x.1.1, y.1.2) :=
            hexagonal_adj_sub_right x.1.1 hay
          have hym : y.1.1 - x.1.1 ∈ box 2 m :=
            hexagonal_adj_mem_box_of_mem_pred hm1 ha hadjSub
          have hyrad : centeredRadius x.1.1 y.1.1 = m := by
            have hym' : siteRadius (y.1.1 - x.1.1) ≤ m :=
              mem_box_iff_siteRadius_le.mp hym
            have hy' : ¬ siteRadius (y.1.1 - x.1.1) ≤ m - 1 := fun hle =>
              hy (mem_box_iff_siteRadius_le.mpr hle)
            change siteRadius (fun i => y.1.1 i - x.1.1 i) = m
            simpa only [Pi.sub_apply] using
              (show siteRadius (y.1.1 - x.1.1) = m by omega)
          refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyrad⟩,
            ReachOpen.step e hopen hpair (ReachOpen.refl y)⟩
  exact hfirst hreach hxInner hbOuter

theorem hexagonalBox_rootShell_imp_centered_of_le
    {n k m : Nat} {omega : ConfigSpace (hexagonalBoxGraph n).edgeSet}
    {x : HexagonalBoxVertex n}
    (hm : m ≤ ((k : Int) - (siteRadius x.1.1 : Int)).natAbs) :
    ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x
        (hexagonalBoxShell n k) →
      ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x
        (hexagonalBoxCenteredShell n x m) := by
  rintro ⟨b, hb, hreach⟩
  have hrb : siteRadius b.1.1 = k := by
    exact siteRadius_eq_of_mem_vertexBoundary (Finset.mem_filter.mp hb).2
  have htri1 := siteRadius_triangle b.1.1 x.1.1
  have htri2 := siteRadius_triangle x.1.1 b.1.1
  rw [centeredRadius_comm b.1.1 x.1.1] at htri2
  have hdist : ((k : Int) - (siteRadius x.1.1 : Int)).natAbs ≤
      centeredRadius x.1.1 b.1.1 := by
    rw [hrb] at htri1 htri2
    by_cases h : siteRadius x.1.1 ≤ k
    · have habs : ((k : Int) - (siteRadius x.1.1 : Int)).natAbs =
          k - siteRadius x.1.1 := by omega
      rw [habs]
      omega
    · have habs : ((k : Int) - (siteRadius x.1.1 : Int)).natAbs =
          siteRadius x.1.1 - k := by omega
      rw [habs]
      omega
  exact hexagonalBox_reachOpen_hits_centered hreach (hm.trans hdist)



theorem hexagonal_rootShell_sum_le_centered_sup
    (n : Nat) (mu : ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet → Real)
    (hmu0 : ∀ omega, 0 ≤ mu omega) (u : HexagonalBoxVertex n) :
    (∑ k : ↑(Finset.Icc 1 n),
      Lindeberg.mean mu (fun omega => if ConnOpenSet
        (hexagonalBoxEndU n) (hexagonalBoxEndV n)
        (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
        u (hexagonalBoxShell n k) then (1 : Real) else 0)) ≤
      2 * (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
        ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
        (fun x => ∑ j ∈ Finset.range n,
          Lindeberg.mean mu (fun omega => if ConnOpenSet
            (hexagonalBoxEndU n) (hexagonalBoxEndV n)
            (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
            x (hexagonalBoxCenteredShell n x j) then (1 : Real) else 0)) := by
  let conn : HexagonalBoxVertex n → Nat → Real := fun x j =>
    Lindeberg.mean mu (fun omega => if ConnOpenSet
      (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      x (hexagonalBoxCenteredShell n x j) then (1 : Real) else 0)
  let qf : Nat → Real := fun k =>
    Lindeberg.mean mu (fun omega => if ConnOpenSet
      (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      u (hexagonalBoxShell n k) then (1 : Real) else 0)
  have hconn0 : ∀ x j, 0 ≤ conn x j := fun x j => mean_indicator_nonneg hmu0 _
  have hrn : siteRadius u.1.1 ≤ n := mem_box_iff_siteRadius_le.mp u.2.1
  change (∑ k : ↑(Finset.Icc 1 n), qf k) ≤
    2 * (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
      ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
      (fun x => ∑ j ∈ Finset.range n, conn x j)
  rw [Finset.sum_coe_sort]
  by_cases hr0 : siteRadius u.1.1 = 0
  · have hcomp0 : ∀ k, 1 ≤ k → qf k ≤ conn u (k - 1) := by
      intro k hk
      apply mean_indicator_mono hmu0
      intro omega homega
      have hm : k - 1 ≤ ((k : Int) - (siteRadius u.1.1 : Int)).natAbs := by
        rw [hr0]
        simp
      exact hexagonalBox_rootShell_imp_centered_of_le hm homega
    have hsum : (∑ k ∈ Finset.Icc 1 n, qf k) ≤
        ∑ j ∈ Finset.range n, conn u j := by
      calc
        _ ≤ ∑ k ∈ Finset.Icc 1 n, conn u (k - 1) :=
          Finset.sum_le_sum fun k hk => hcomp0 k (Finset.mem_Icc.mp hk).1
        _ = _ := sum_Icc_one_pred_eq_sum_range (conn u) n
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range n, conn u j :=
      Finset.sum_nonneg fun j _ => hconn0 u j
    have hsup := Finset.le_sup'
      (fun x => ∑ j ∈ Finset.range n, conn x j) (Finset.mem_univ u)
    linarith
  · have hr1 : 1 ≤ siteRadius u.1.1 := Nat.one_le_iff_ne_zero.mpr hr0
    apply revealment_sum_bound_range (Finset.univ : Finset (HexagonalBoxVertex n))
      ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩ conn hconn0 n
      (siteRadius u.1.1) hr1 hrn u (Finset.mem_univ u) qf
    intro k
    apply mean_indicator_mono hmu0
    intro omega homega
    exact hexagonalBox_rootShell_imp_centered_of_le le_rfl homega

noncomputable def hexagonalCenteredDenom
    (n : Nat) (q beta : Real) : Real :=
  4 * (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ j ∈ Finset.range n,
      hexagonalOuterCenteredConn n q beta x j) / (n : Real)

theorem hexagonalOuterCenteredConn_nonneg
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (x : HexagonalBoxVertex n) (j : Nat) :
    0 ≤ hexagonalOuterCenteredConn n q beta x j := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) omega).le
  unfold hexagonalOuterCenteredConn
  exact mean_indicator_nonneg hmu0 _

theorem hexagonalOuterCenteredConn_zero
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (x : HexagonalBoxVertex n) :
    hexagonalOuterCenteredConn n q beta x 0 = 1 := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq)
  have hall : (fun omega : ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet =>
      if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n)
        (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
        x (hexagonalBoxCenteredShell n x 0) then (1 : Real) else 0) =
      fun _ => 1 := by
    funext omega
    rw [if_pos]
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, centeredRadius_self x.1.1⟩,
      ReachOpen.refl x⟩
  unfold hexagonalOuterCenteredConn
  rw [hall]
  exact Lindeberg.mean_const mu hmu1 1

theorem hexagonalOuterCenteredConn_le_one
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (x : HexagonalBoxVertex n) (j : Nat) :
    hexagonalOuterCenteredConn n q beta x j ≤ 1 := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq)
  calc
    hexagonalOuterCenteredConn n q beta x j ≤
        Lindeberg.mean mu (fun _ => (1 : Real)) := by
      unfold hexagonalOuterCenteredConn Lindeberg.mean
      apply Finset.sum_le_sum
      intro omega _
      apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
      change (if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n)
        (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
        x (hexagonalBoxCenteredShell n x j) then (1 : Real) else 0) ≤ 1
      split_ifs <;> norm_num
    _ = 1 := Lindeberg.mean_const mu hmu1 1

theorem hexagonalOuterCenteredConn_antitone
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (x : HexagonalBoxVertex n) :
    Antitone (hexagonalOuterCenteredConn n q beta x) := by
  intro j k hjk
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) omega).le
  unfold hexagonalOuterCenteredConn
  apply mean_indicator_mono hmu0
  intro omega hconn
  obtain ⟨b, hb, hreach⟩ := hconn
  have hrad : centeredRadius x.1.1 b.1.1 = k := (Finset.mem_filter.mp hb).2
  exact hexagonalBox_reachOpen_hits_centered hreach (hjk.trans_eq hrad.symm)

theorem hexagonalOuterInnerTheta_nonneg
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) (k : Nat) :
    0 ≤ hexagonalOuterInnerTheta q beta k := by
  by_cases hk : k = 0
  · simp [hexagonalOuterInnerTheta, hk]
  rw [hexagonalOuterInnerTheta, if_neg hk]
  unfold hexagonalInnerCrossInd Lindeberg.mean
  apply Finset.sum_nonneg
  intro omega _
  apply mul_nonneg
  · change 0 ≤ (openCrossEvent (hexagonalBoxEndU k) (hexagonalBoxEndV k)
      (hexagonalBoxRoot k) (hexagonalBoxShell k k)).indicator
      (fun _ => (1 : Real))
      (restrictConfig (hexagonalBoxEdgeLE (by omega : k ≤ 2 * k)) omega)
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  · exact (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) omega).le

@[simp] theorem hexagonalOuterInnerTheta_zero (q beta : Real) :
    hexagonalOuterInnerTheta q beta 0 = 1 := by
  simp [hexagonalOuterInnerTheta]



theorem hexagonalCenteredShellEvent_iff_innerCross
    (k : Nat) (hk : 1 ≤ k)
    (omega : ConfigSpace (hexagonalBoxGraph (2 * k)).edgeSet) :
    omega ∈ hexagonalCenteredShellEvent (2 * k) k ↔
      restrictConfig (hexagonalBoxEdgeLE (by omega : k ≤ 2 * k)) omega ∈
        openCrossEvent (hexagonalBoxEndU k) (hexagonalBoxEndV k)
          (hexagonalBoxRoot k) (hexagonalBoxShell k k) := by
  let incl : HexagonalBoxVertex k → HexagonalBoxVertex (2 * k) :=
    hexagonalBoxVertInclLE (by omega)
  let iota := hexagonalBoxEdgeLE (by omega : k ≤ 2 * k)
  constructor
  · rintro ⟨b, hb, hreach⟩
    have hbOuter : b.1.1 ∉ box 2 (k - 1) := (Finset.mem_filter.mp hb).2.2
    have hroot : (hexagonalBoxRoot (2 * k)).1.1 ∈ box 2 (k - 1) := by
      intro j
      simp [hexagonalBoxRoot]
    have hfirst : ∀ {a b : HexagonalBoxVertex (2 * k)},
        ReachOpen (hexagonalBoxEndU (2 * k)) (hexagonalBoxEndV (2 * k))
          omega a b →
        ∀ (ha : a.1.1 ∈ box 2 (k - 1)), b.1.1 ∉ box 2 (k - 1) →
        ConnOpenSet (hexagonalBoxEndU k) (hexagonalBoxEndV k)
          (restrictConfig iota omega)
          ⟨a.1, ⟨box_mono 2 (by omega : k - 1 ≤ k) ha,
            Set.mem_univ _⟩⟩
          (hexagonalBoxShell k k) := by
      intro a b hr
      induction hr with
      | refl a => intro ha hnot; exact (hnot ha).elim
      | @step a y z e hopen hpair hrest ih =>
          intro ha hz
          have hay : (hexagonalBoxGraph (2 * k)).Adj a y := by
            rcases hpair with hpair | hpair
            · rw [← hpair.1, ← hpair.2]
              exact hexagonalBox_end_adj (2 * k) e
            · rw [← hpair.1, ← hpair.2]
              exact (hexagonalBox_end_adj (2 * k) e).symm
          have hak : a.1.1 ∈ box 2 k := box_mono 2 (by omega) ha
          by_cases hy : y.1.1 ∈ box 2 (k - 1)
          · obtain ⟨w, hw, hwy⟩ := ih hy hz
            let ai : HexagonalBoxVertex k :=
              ⟨a.1, ⟨hak, Set.mem_univ _⟩⟩
            let yi : HexagonalBoxVertex k :=
              ⟨y.1, ⟨box_mono 2 (by omega : k - 1 ≤ k) hy,
                Set.mem_univ _⟩⟩
            let ei : (hexagonalBoxGraph k).edgeSet :=
              ⟨s(ai, yi), by
                rw [SimpleGraph.mem_edgeSet]
                exact hay⟩
            have hei : iota ei = e := by
              apply Subtype.ext
              have hedgeEq : e.1 = s(a, y) := by
                have hout : s(hexagonalBoxEndU (2 * k) e,
                    hexagonalBoxEndV (2 * k) e) = e.1 := e.1.out_eq
                rcases hpair with hp | hp
                · simpa [hp.1, hp.2] using hout.symm
                · simpa [hp.1, hp.2, Sym2.eq_swap] using hout.symm
              change Sym2.map (hexagonalBoxVertInclLE (by omega : k ≤ 2 * k))
                ei.1 = e.1
              have hia : hexagonalBoxVertInclLE (by omega : k ≤ 2 * k) ai = a :=
                Subtype.ext (by rfl)
              have hiy : hexagonalBoxVertInclLE (by omega : k ≤ 2 * k) yi = y :=
                Subtype.ext (by rfl)
              rw [show ei.1 = s(ai, yi) from rfl, Sym2.map_mk,
                hia, hiy, ← hedgeEq]
            have heiOpen : restrictConfig iota omega ei = true := by
              change omega (iota ei) = true
              rw [hei]
              exact hopen
            have heEnds :
                ((hexagonalBoxEndU k ei = ai ∧ hexagonalBoxEndV k ei = yi) ∨
                 (hexagonalBoxEndU k ei = yi ∧ hexagonalBoxEndV k ei = ai)) := by
              have hout := ei.1.out_eq
              change s(hexagonalBoxEndU k ei, hexagonalBoxEndV k ei) =
                s(ai, yi) at hout
              exact Sym2.eq_iff.mp hout
            have htail : ReachOpen (hexagonalBoxEndU k) (hexagonalBoxEndV k)
                (restrictConfig iota omega) yi w := by
              simpa [yi] using hwy
            refine ⟨w, hw, ?_⟩
            simpa [ai] using ReachOpen.step ei heiOpen heEnds htail
          · have hyk : y.1.1 ∈ box 2 k :=
              hexagonal_adj_mem_box_of_mem_pred hk ha hay
            let ai : HexagonalBoxVertex k :=
              ⟨a.1, ⟨hak, Set.mem_univ _⟩⟩
            let yi : HexagonalBoxVertex k :=
              ⟨y.1, ⟨hyk, Set.mem_univ _⟩⟩
            let ei : (hexagonalBoxGraph k).edgeSet :=
              ⟨s(ai, yi), by rw [SimpleGraph.mem_edgeSet]; exact hay⟩
            have hei : iota ei = e := by
              apply Subtype.ext
              have hedgeEq : e.1 = s(a, y) := by
                have hout : s(hexagonalBoxEndU (2 * k) e,
                    hexagonalBoxEndV (2 * k) e) = e.1 := e.1.out_eq
                rcases hpair with hp | hp
                · simpa [hp.1, hp.2] using hout.symm
                · simpa [hp.1, hp.2, Sym2.eq_swap] using hout.symm
              change Sym2.map (hexagonalBoxVertInclLE (by omega : k ≤ 2 * k))
                ei.1 = e.1
              have hia : hexagonalBoxVertInclLE (by omega : k ≤ 2 * k) ai = a :=
                Subtype.ext (by rfl)
              have hiy : hexagonalBoxVertInclLE (by omega : k ≤ 2 * k) yi = y :=
                Subtype.ext (by rfl)
              rw [show ei.1 = s(ai, yi) from rfl, Sym2.map_mk,
                hia, hiy, ← hedgeEq]
            have heiOpen : restrictConfig iota omega ei = true := by
              change omega (iota ei) = true
              rw [hei]
              exact hopen
            have heEnds :
                ((hexagonalBoxEndU k ei = ai ∧ hexagonalBoxEndV k ei = yi) ∨
                 (hexagonalBoxEndU k ei = yi ∧ hexagonalBoxEndV k ei = ai)) := by
              have hout := ei.1.out_eq
              change s(hexagonalBoxEndU k ei, hexagonalBoxEndV k ei) =
                s(ai, yi) at hout
              exact Sym2.eq_iff.mp hout
            refine ⟨yi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyk, hy⟩, ?_⟩
            simpa [ai] using ReachOpen.step ei heiOpen heEnds (ReachOpen.refl yi)
    simpa [incl, iota, hexagonalBoxRoot] using hfirst hreach hroot hbOuter
  · rintro ⟨b, hb, hreach⟩
    have hlift : ∀ {a b : HexagonalBoxVertex k},
        ReachOpen (hexagonalBoxEndU k) (hexagonalBoxEndV k)
          (restrictConfig iota omega) a b →
        ReachOpen (hexagonalBoxEndU (2 * k)) (hexagonalBoxEndV (2 * k))
          omega (incl a) (incl b) := by
      intro a b hr
      induction hr with
      | refl a => exact ReachOpen.refl (incl a)
      | @step a y z e hopen hpair hrest ih =>
          let eo := iota e
          have heoOpen : omega eo = true := hopen
          have hepairInner : e.1 = s(a, y) := by
            have hout : s(hexagonalBoxEndU k e, hexagonalBoxEndV k e) = e.1 :=
              e.1.out_eq
            rcases hpair with hp | hp
            · simpa [hp.1, hp.2] using hout.symm
            · simpa [hp.1, hp.2, Sym2.eq_swap] using hout.symm
          have heoPair : eo.1 = s(incl a, incl y) := by
            change Sym2.map (hexagonalBoxVertInclLE (by omega : k ≤ 2 * k)) e.1 =
              s(incl a, incl y)
            rw [hepairInner, Sym2.map_mk]
          have heEnds :
              ((hexagonalBoxEndU (2 * k) eo = incl a ∧
                hexagonalBoxEndV (2 * k) eo = incl y) ∨
               (hexagonalBoxEndU (2 * k) eo = incl y ∧
                hexagonalBoxEndV (2 * k) eo = incl a)) := by
            have hout : s(hexagonalBoxEndU (2 * k) eo,
                hexagonalBoxEndV (2 * k) eo) = eo.1 := eo.1.out_eq
            rw [heoPair] at hout
            exact Sym2.eq_iff.mp hout
          exact ReachOpen.step eo heoOpen heEnds ih
    refine ⟨incl b, ?_, hlift hreach⟩
    have hb' := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'.1,
      fun hsmall => hb'.2 hsmall⟩

theorem hexagonalCenteredFullMass_eq_outerInnerTheta
    (k : Nat) (hk : 1 ≤ k) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex (2 * k))),
        (hexagonalCenteredShellFullEvent (2 * k) k).indicator
            (fun _ => (1 : Real)) omega *
          FK.wiredFkProb (hexagonalBoxGraph (2 * k))
            (fun y => y ∈ hexagonalBoxShell (2 * k) (2 * k))
            (1 - Real.exp (-beta)) q omega) =
      hexagonalOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  let G := hexagonalBoxGraph (2 * k)
  let boundary : HexagonalBoxVertex (2 * k) → Prop :=
    fun y => y ∈ hexagonalBoxShell (2 * k) (2 * k)
  let A := hexagonalCenteredShellEvent (2 * k) k
  have hparam : FK.betaParams
      (fun _ : Sym2 (HexagonalBoxVertex (2 * k)) => (1 : Real)) beta =
      fun _ => p := by
    funext e
    simp [FK.betaParams, p]
  have hmean := FK.activeBCMean_boundaryClique_eq_wired
    G boundary hp hp1 hq0 (A.indicator fun _ => (1 : Real))
  have hevent : hexagonalInnerCrossInd k =
      A.indicator (fun _ => (1 : Real)) := by
    funext omega
    unfold hexagonalInnerCrossInd
    rw [Set.indicator_apply, Set.indicator_apply]
    have hiff := hexagonalCenteredShellEvent_iff_innerCross k hk omega
    by_cases h : omega ∈ A
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hi => h (hiff.mpr hi))]
  have hactive :
      FK.activeBCMean G (boundaryCliqueGraph boundary) (fun _ => p) q
          (A.indicator fun _ => (1 : Real)) =
        hexagonalOuterInnerTheta q beta k := by
    have hk0 : k ≠ 0 := by omega
    rw [hexagonalOuterInnerTheta, if_neg hk0, ← hevent, hparam]
    rfl
  rw [← hactive]
  rw [hmean]
  apply Finset.sum_congr rfl
  intro omega _
  have hpre := restrictActive_preimage_hexagonalCenteredShellEvent (2 * k) k
  have hiff : restrictActive G omega ∈ A ↔
      omega ∈ hexagonalCenteredShellFullEvent (2 * k) k := by
    rw [← Set.mem_preimage]
    exact Set.ext_iff.mp hpre omega
  by_cases h : restrictActive G omega ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hf => h (hiff.mpr hf))]

theorem hexagonal_centeredConn_imp_transShell
    {n k : Nat} (x : HexagonalBoxVertex n) (hk : 1 ≤ k)
    (hkn : 2 * k < n)
    (rho : ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet)
    (hconn : ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) rho)
      x (hexagonalBoxCenteredShell n x k)) :
    let hsub := hexagonalTransBox_subset_double x.2.1 hkn
    let transIncl := hexagonalTransBoxIncl hsub
    let hadjm := ocd_comapAdjMatch hexagonalGraph transIncl (fun _ => rfl)
    ocd_innerRestrictActive (hexagonalTransBoxGraph (2 * k) x.1.1)
        (hexagonalBoxGraph (2 * n)) transIncl hadjm rho ∈
      hexagonalTransShellEvent (2 * k) k x.1 := by
  let hsub := hexagonalTransBox_subset_double x.2.1 hkn
  let transIncl := hexagonalTransBoxIncl hsub
  let hadjm := ocd_comapAdjMatch hexagonalGraph transIncl (fun _ => rfl)
  let transCfg := ocd_innerRestrictActive
    (hexagonalTransBoxGraph (2 * k) x.1.1)
    (hexagonalBoxGraph (2 * n)) transIncl hadjm rho
  let iotaN := hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)
  obtain ⟨b, hb, hreach⟩ := hconn
  have hbRad : centeredRadius x.1.1 b.1.1 = k := (Finset.mem_filter.mp hb).2
  have hbOuter : b.1.1 - x.1.1 ∉ box 2 (k - 1) := by
    intro hbIn
    have hbLe : centeredRadius x.1.1 b.1.1 ≤ k - 1 := by
      have := mem_box_iff_siteRadius_le.mp hbIn
      change siteRadius (fun i => b.1.1 i - x.1.1 i) ≤ k - 1
      simpa only [Pi.sub_apply] using this
    omega
  have hxInner : x.1.1 - x.1.1 ∈ box 2 (k - 1) := by simp
  have hfirst : ∀ {a b : HexagonalBoxVertex n},
      ReachOpen (hexagonalBoxEndU n) (hexagonalBoxEndV n)
        (restrictConfig iotaN rho) a b →
      ∀ (ha : a.1.1 - x.1.1 ∈ box 2 (k - 1)),
        b.1.1 - x.1.1 ∉ box 2 (k - 1) →
      ConnOpenSet (hexagonalTransBoxEndU (2 * k) x.1.1)
        (hexagonalTransBoxEndV (2 * k) x.1.1) transCfg
        ⟨a.1, ⟨by
          apply box_mono 2 (by omega : k - 1 ≤ 2 * k)
          exact ha, Set.mem_univ _⟩⟩
        (hexagonalTransBoxShell (2 * k) k x.1.1) := by
    intro a b hr
    induction hr with
    | refl a => intro ha hnot; exact (hnot ha).elim
    | @step a y z e hopen hpair hrest ih =>
        intro ha hz
        have hay : (hexagonalBoxGraph n).Adj a y := by
          rcases hpair with hp | hp
          · rw [← hp.1, ← hp.2]
            exact hexagonalBox_end_adj n e
          · rw [← hp.1, ← hp.2]
            exact (hexagonalBox_end_adj n e).symm
        have hadjSub : hexagonalGraph.Adj
            (a.1.1 - x.1.1, a.1.2) (y.1.1 - x.1.1, y.1.2) :=
          hexagonal_adj_sub_right x.1.1 hay
        have hak : a.1.1 - x.1.1 ∈ box 2 k := box_mono 2 (by omega) ha
        by_cases hy : y.1.1 - x.1.1 ∈ box 2 (k - 1)
        · obtain ⟨w, hw, hwy⟩ := ih hy hz
          let av : HexagonalTransBoxVertex (2 * k) x.1.1 :=
            ⟨a.1, ⟨box_mono 2 (by omega : k ≤ 2 * k) hak,
              Set.mem_univ _⟩⟩
          have hyk : y.1.1 - x.1.1 ∈ box 2 k := box_mono 2 (by omega) hy
          let yt : HexagonalTransBoxVertex (2 * k) x.1.1 :=
            ⟨y.1, ⟨box_mono 2 (by omega : k ≤ 2 * k) hyk,
              Set.mem_univ _⟩⟩
          let et : (hexagonalTransBoxGraph (2 * k) x.1.1).edgeSet :=
            ⟨s(av, yt), by rw [SimpleGraph.mem_edgeSet]; exact hay⟩
          let etOut : (hexagonalBoxGraph (2 * n)).edgeSet :=
            ⟨ocd_innerEdge transIncl et.1, by
              unfold ocd_innerEdge
              rw [show et.1 = s(av, yt) from rfl, Sym2.map_mk,
                SimpleGraph.mem_edgeSet]
              change hexagonalGraph.Adj (transIncl av).1 (transIncl yt).1
              exact hay⟩
          have hedgeSource : e.1 = s(a, y) := by
            have hout : s(hexagonalBoxEndU n e, hexagonalBoxEndV n e) = e.1 :=
              e.1.out_eq
            rcases hpair with hp | hp
            · simpa [hp.1, hp.2] using hout.symm
            · simpa [hp.1, hp.2, Sym2.eq_swap] using hout.symm
          have houtEq : etOut = iotaN e := by
            apply Subtype.ext
            change Sym2.map transIncl et.1 =
              Sym2.map (hexagonalBoxVertInclLE (by omega)) e.1
            have hta : transIncl av = hexagonalBoxVertInclLE
                (by omega : n ≤ 2 * n) a := Subtype.ext (by rfl)
            have hty : transIncl yt = hexagonalBoxVertInclLE
                (by omega : n ≤ 2 * n) y := Subtype.ext (by rfl)
            rw [show et.1 = s(av, yt) from rfl,
              Sym2.map_mk, hedgeSource, Sym2.map_mk, hta, hty]
          have etOpen : transCfg et = true := by
            change rho etOut = true
            rw [houtEq]
            exact hopen
          have etEnds :
              ((hexagonalTransBoxEndU (2 * k) x.1.1 et = av ∧
                hexagonalTransBoxEndV (2 * k) x.1.1 et = yt) ∨
               (hexagonalTransBoxEndU (2 * k) x.1.1 et = yt ∧
                hexagonalTransBoxEndV (2 * k) x.1.1 et = av)) := by
            have hout := et.1.out_eq
            change s(hexagonalTransBoxEndU (2 * k) x.1.1 et,
              hexagonalTransBoxEndV (2 * k) x.1.1 et) = s(av, yt) at hout
            exact Sym2.eq_iff.mp hout
          have htail : ReachOpen (hexagonalTransBoxEndU (2 * k) x.1.1)
              (hexagonalTransBoxEndV (2 * k) x.1.1) transCfg yt w := by
            simpa [yt] using hwy
          refine ⟨w, hw, ?_⟩
          simpa [av] using ReachOpen.step et etOpen etEnds htail
        · have hyk : y.1.1 - x.1.1 ∈ box 2 k :=
            hexagonal_adj_mem_box_of_mem_pred hk ha hadjSub
          let av : HexagonalTransBoxVertex (2 * k) x.1.1 :=
            ⟨a.1, ⟨box_mono 2 (by omega : k ≤ 2 * k) hak,
              Set.mem_univ _⟩⟩
          let yt : HexagonalTransBoxVertex (2 * k) x.1.1 :=
            ⟨y.1, ⟨box_mono 2 (by omega : k ≤ 2 * k) hyk,
              Set.mem_univ _⟩⟩
          let et : (hexagonalTransBoxGraph (2 * k) x.1.1).edgeSet :=
            ⟨s(av, yt), by rw [SimpleGraph.mem_edgeSet]; exact hay⟩
          let etOut : (hexagonalBoxGraph (2 * n)).edgeSet :=
            ⟨ocd_innerEdge transIncl et.1, by
              unfold ocd_innerEdge
              rw [show et.1 = s(av, yt) from rfl, Sym2.map_mk,
                SimpleGraph.mem_edgeSet]
              change hexagonalGraph.Adj (transIncl av).1 (transIncl yt).1
              exact hay⟩
          have hedgeSource : e.1 = s(a, y) := by
            have hout : s(hexagonalBoxEndU n e, hexagonalBoxEndV n e) = e.1 :=
              e.1.out_eq
            rcases hpair with hp | hp
            · simpa [hp.1, hp.2] using hout.symm
            · simpa [hp.1, hp.2, Sym2.eq_swap] using hout.symm
          have houtEq : etOut = iotaN e := by
            apply Subtype.ext
            change Sym2.map transIncl et.1 =
              Sym2.map (hexagonalBoxVertInclLE (by omega)) e.1
            have hta : transIncl av = hexagonalBoxVertInclLE
                (by omega : n ≤ 2 * n) a := Subtype.ext (by rfl)
            have hty : transIncl yt = hexagonalBoxVertInclLE
                (by omega : n ≤ 2 * n) y := Subtype.ext (by rfl)
            rw [show et.1 = s(av, yt) from rfl,
              Sym2.map_mk, hedgeSource, Sym2.map_mk, hta, hty]
          have etOpen : transCfg et = true := by
            change rho etOut = true
            rw [houtEq]
            exact hopen
          have etEnds :
              ((hexagonalTransBoxEndU (2 * k) x.1.1 et = av ∧
                hexagonalTransBoxEndV (2 * k) x.1.1 et = yt) ∨
               (hexagonalTransBoxEndU (2 * k) x.1.1 et = yt ∧
                hexagonalTransBoxEndV (2 * k) x.1.1 et = av)) := by
            have hout := et.1.out_eq
            change s(hexagonalTransBoxEndU (2 * k) x.1.1 et,
              hexagonalTransBoxEndV (2 * k) x.1.1 et) = s(av, yt) at hout
            exact Sym2.eq_iff.mp hout
          have etMem : yt ∈ hexagonalTransBoxShell (2 * k) k x.1.1 := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyk, ?_⟩
            intro hsmall
            exact hy hsmall
          refine ⟨yt, etMem, ?_⟩
          simpa [av] using ReachOpen.step et etOpen etEnds (ReachOpen.refl yt)
  have hresult := hfirst hreach hxInner hbOuter
  simpa [transCfg, transIncl, hsub, hadjm, iotaN,
    hexagonalTransShellEvent, hexagonalTransBoxCenter] using hresult

theorem hexagonalOuterCenteredConn_le_theta_strict
    (n k : Nat) (x : HexagonalBoxVertex n)
    (hk : 1 ≤ k) (hkn : 2 * k < n)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonalOuterCenteredConn n q beta x k ≤
      hexagonalOuterInnerTheta q beta k := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let hsub := hexagonalTransBox_subset_double x.2.1 hkn
  let transIncl := hexagonalTransBoxIncl hsub
  let hadjm := ocd_comapAdjMatch hexagonalGraph transIncl (fun _ => rfl)
  let A := hexagonalTransShellEvent (2 * k) k x.1
  let obs : ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet → Real := fun rho =>
    A.indicator (fun _ => (1 : Real))
      (ocd_innerRestrictActive (hexagonalTransBoxGraph (2 * k) x.1.1)
        (hexagonalBoxGraph (2 * n)) transIncl hadjm rho)
  have hmu0 : ∀ rho, 0 ≤ mu rho := fun rho =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) rho).le
  have hleft : hexagonalOuterCenteredConn n q beta x k ≤
      Lindeberg.mean mu obs := by
    unfold hexagonalOuterCenteredConn
    apply mean_indicator_mono hmu0
    intro rho hconn
    exact hexagonal_centeredConn_imp_transShell x hk hkn rho hconn
  have hdom := hexagonalTransBox_activeBCMean_le x.2.1 hk hkn q beta hq hbeta
    (hexagonalTransShellEvent_increasing (2 * k) k x.1)
  have htrans := hexagonalTransShellEvent_betaMean_eq_centeredFullMass
    (2 * k) k x.1 q beta (zero_lt_one.trans_le hq) hbeta
  have hcenter := hexagonalCenteredFullMass_eq_outerInnerTheta
    k hk q beta hq hbeta
  calc
    hexagonalOuterCenteredConn n q beta x k ≤ Lindeberg.mean mu obs := hleft
    _ ≤ FK.activeBCMean (hexagonalTransBoxGraph (2 * k) x.1.1)
        (boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x.1.1))
        (FK.betaParams (fun _ => 1) beta) q
        (A.indicator fun _ => (1 : Real)) := by
      simpa [mu, obs, A, transIncl, hsub, hadjm,
        hexagonalBoxBoundaryGraph] using hdom
    _ = hexagonalOuterInnerTheta q beta k := by
      rw [show FK.activeBCMean (hexagonalTransBoxGraph (2 * k) x.1.1)
          (boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x.1.1))
          (FK.betaParams (fun _ => 1) beta) q
          (A.indicator fun _ => (1 : Real)) =
          ∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex (2 * k))),
            (hexagonalCenteredShellFullEvent (2 * k) k).indicator
                (fun _ => (1 : Real)) omega *
              FK.wiredFkProb (hexagonalBoxGraph (2 * k))
                (fun y => y ∈ hexagonalBoxShell (2 * k) (2 * k))
                (1 - Real.exp (-beta)) q omega by
        simpa [A] using htrans]
      exact hcenter

theorem hexagonalCenteredDenom_pos
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    0 < hexagonalCenteredDenom n q beta := by
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ j ∈ Finset.range n,
      hexagonalOuterCenteredConn n q beta x j)
  have hsum : 1 ≤ ∑ j ∈ Finset.range n,
      hexagonalOuterCenteredConn n q beta (hexagonalBoxRoot n) j := by
    rw [← hexagonalOuterCenteredConn_zero n q beta hq hbeta
      (hexagonalBoxRoot n)]
    apply Finset.single_le_sum
      (fun j _ => hexagonalOuterCenteredConn_nonneg n q beta hq hbeta _ j)
    simpa using hn
  have hsup := Finset.le_sup'
    (fun x => ∑ j ∈ Finset.range n,
      hexagonalOuterCenteredConn n q beta x j)
    (Finset.mem_univ (hexagonalBoxRoot n))
  have hM : 0 < M := by change _ ≤ M at hsup; linarith
  have hnR : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  unfold hexagonalCenteredDenom
  change 0 < 4 * M / (n : Real)
  positivity



theorem hexagonal_outer_inner_hcov_centered
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (hexagonalInnerCrossInd n) *
        (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) /
          hexagonalCenteredDenom n q beta ≤
      ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ j ∈ Finset.range n,
      hexagonalOuterCenteredConn n q beta x j)
  let D := 4 * M / (n : Real)
  have hD : 0 < D := by
    simpa [hexagonalCenteredDenom, M, D] using
      hexagonalCenteredDenom_pos n hn q beta hq hbeta
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) omega).le
  have hsum : ∀ e : (hexagonalBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega => if ConnOpenSet
          (hexagonalBoxEndU n) (hexagonalBoxEndV n)
          (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (hexagonalBoxEndU n e) (hexagonalBoxShell n k)
          then (1 : Real) else 0) +
        Lindeberg.mean mu (fun omega => if ConnOpenSet
          (hexagonalBoxEndU n) (hexagonalBoxEndV n)
          (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (hexagonalBoxEndV n e) (hexagonalBoxShell n k)
          then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro e
    have hu := hexagonal_rootShell_sum_le_centered_sup n mu hmu0
      (hexagonalBoxEndU n e)
    have hv := hexagonal_rootShell_sum_le_centered_sup n mu hmu0
      (hexagonalBoxEndV n e)
    change _ ≤ 2 * M at hu hv
    have hcard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [Finset.sum_add_distrib, hcard]
    change _ ≤ (n : Real) * (4 * M / (n : Real))
    have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    rw [mul_div_cancel₀ _ hnR.ne']
    linarith
  have hmain := hexagonal_outer_inner_hcov n hn q beta D hq hbeta hD
    (by simpa [mu] using hsum)
  simpa [hexagonalCenteredDenom, mu, M, D] using hmain



theorem hexagonal_centered_sup_le_two_sig_of_strict_comparison
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      hexagonalOuterCenteredConn n q beta x k ≤
        hexagonalOuterInnerTheta q beta k) :
    (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
        ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
        (fun x => ∑ j ∈ Finset.range n,
          hexagonalOuterCenteredConn n q beta x j) ≤
      2 * hexagonalOuterInnerSig n q beta := by
  apply Finset.sup'_le
  intro x hx
  exact StatMech.OSSS.antitone_sum_range_le_two_profile_strict
    (hexagonalOuterCenteredConn n q beta x)
    (hexagonalOuterInnerTheta q beta)
    (hexagonalOuterCenteredConn_nonneg n q beta hq hbeta x)
    (hexagonalOuterCenteredConn_antitone n q beta hq hbeta x)
    (hexagonalOuterInnerTheta_nonneg q beta hq hbeta) n
    (by rw [hexagonalOuterCenteredConn_zero n q beta hq hbeta x,
      hexagonalOuterInnerTheta_zero])
    (fun k hk hstrict => hcomp x k hk hstrict)
    (fun k hk => by
      rw [hexagonalOuterInnerTheta_zero]
      exact hexagonalOuterCenteredConn_le_one n q beta hq hbeta x k)

theorem hexagonalCenteredDenom_le_eight_sig_of_strict_comparison
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      hexagonalOuterCenteredConn n q beta x k ≤
        hexagonalOuterInnerTheta q beta k) :
    hexagonalCenteredDenom n q beta ≤
      8 * hexagonalOuterInnerSig n q beta / (n : Real) := by
  have hsup := hexagonal_centered_sup_le_two_sig_of_strict_comparison
    n q beta hq hbeta hcomp
  unfold hexagonalCenteredDenom
  calc
    4 * (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
          ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
          (fun x => ∑ j ∈ Finset.range n,
            hexagonalOuterCenteredConn n q beta x j) / (n : Real) ≤
        4 * (2 * hexagonalOuterInnerSig n q beta) / (n : Real) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsup (by norm_num)) (Nat.cast_nonneg n)
    _ = 8 * hexagonalOuterInnerSig n q beta / (n : Real) := by ring

theorem hexagonal_outer_inner_hcov_sharp_of_strict_comparison
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      hexagonalOuterCenteredConn n q beta x k ≤
        hexagonalOuterInnerTheta q beta k) :
    let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (hexagonalInnerCrossInd n) *
        (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤
      ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let theta := Lindeberg.mean mu (hexagonalInnerCrossInd n)
  have htheta0 : 0 ≤ theta := by
    unfold theta hexagonalInnerCrossInd Lindeberg.mean
    exact Finset.sum_nonneg fun omega _ => mul_nonneg (by
      change 0 ≤ (openCrossEvent (hexagonalBoxEndU n) (hexagonalBoxEndV n)
        (hexagonalBoxRoot n) (hexagonalBoxShell n n)).indicator
        (fun _ => (1 : Real))
        (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      rw [Set.indicator_apply]
      split_ifs <;> norm_num) (FK.activeBCProb_pos _ _
        (FK.betaParams_pos (fun _ => by norm_num) hbeta)
        (FK.betaParams_lt_one (fun _ => 1) beta)
        (zero_lt_one.trans_le hq) omega).le
  have htheta1 : theta ≤ 1 := by
    let mu1 := FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    have hmu0 : ∀ omega, 0 ≤ mu1 omega := fun omega =>
      (FK.activeBCProb_pos _ _
        (FK.betaParams_pos (fun _ => by norm_num) hbeta)
        (FK.betaParams_lt_one (fun _ => 1) beta)
        (zero_lt_one.trans_le hq) omega).le
    have hmu1 : ∑ omega, mu1 omega = 1 :=
      FK.activeBCProb_sum_eq_one _ _
        (FK.betaParams_pos (fun _ => by norm_num) hbeta)
        (FK.betaParams_lt_one (fun _ => 1) beta)
        (zero_lt_one.trans_le hq)
    calc
      theta ≤ Lindeberg.mean mu1 (fun _ => (1 : Real)) := by
        unfold theta hexagonalInnerCrossInd Lindeberg.mean mu mu1
        apply Finset.sum_le_sum
        intro omega _
        apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
        change (openCrossEvent (hexagonalBoxEndU n) (hexagonalBoxEndV n)
          (hexagonalBoxRoot n) (hexagonalBoxShell n n)).indicator
          (fun _ => (1 : Real))
          (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega) ≤ 1
        rw [Set.indicator_apply]
        split_ifs <;> norm_num
      _ = 1 := Lindeberg.mean_const mu1 hmu1 1
  have hnum : 0 ≤ theta * (1 - theta) :=
    mul_nonneg htheta0 (sub_nonneg.mpr htheta1)
  have hDpos := hexagonalCenteredDenom_pos n hn q beta hq hbeta
  have hDle := hexagonalCenteredDenom_le_eight_sig_of_strict_comparison
    n q beta hq hbeta hcomp
  have hfrac : theta * (1 - theta) /
      (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤
      theta * (1 - theta) / hexagonalCenteredDenom n q beta :=
    div_le_div_of_nonneg_left hnum hDpos hDle
  have hbase := hexagonal_outer_inner_hcov_centered n hn q beta hq hbeta
  exact hfrac.trans (by simpa [mu, theta] using hbase)

theorem hexagonal_outer_inner_differential_sharp_of_strict_comparison
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      hexagonalOuterCenteredConn n q beta x k ≤
        hexagonalOuterInnerTheta q beta k) :
    hexagonalOuterInnerTheta q beta n *
        (1 - hexagonalOuterInnerTheta q beta n) /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  letI : Nonempty (hexagonalBoxGraph (2 * n)).edgeSet :=
    hexagonalBoxGraph_edgeSet_nonempty (2 * n) (by omega)
  let G := hexagonalBoxGraph (2 * n)
  let C := hexagonalBoxBoundaryGraph (2 * n)
  let J : Sym2 (HexagonalBoxVertex (2 * n)) → Real := fun _ => 1
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let f := hexagonalInnerCrossInd n
  have hJ : ∀ e, 0 < J e := fun _ => by simp [J]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) /
        (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
    simpa [G, C, J, mu, f] using
      hexagonal_outer_inner_hcov_sharp_of_strict_comparison
        n hn q beta hq hbeta hcomp
  have hpos : ∀ omega, 0 < mu omega :=
    FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    FK.activeBCProb_FKGLatticeCondition G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq
  have hf : Monotone f := hexagonalInnerCrossInd_monotone n
  have hcov0 : ∀ e : G.edgeSet,
      0 ≤ FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← StatMech.OSSS.ActiveBoundaryDifferential.cov_activeBC_eq]
    exact LindebergTree.cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := FK.hasDerivAt_activeBCMean_beta_sum G C hJ hbeta hq0 f
  have hderivEq :
      deriv (fun b => FK.activeBCMean G C (FK.betaParams J b) q f) beta =
        ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
          FK.activeBCCov G C (FK.betaParams J beta) q f
            (Lindeberg.coord e) := by
    rw [hderiv.deriv]
    simp only [FK.betaParams]
  have hpref : ∀ e : G.edgeSet,
      (1 : Real) ≤ J e.1 / (1 - Real.exp (-(beta * J e.1))) := by
    intro e
    have hden : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    simp only [J, mul_one]
    rw [le_div_iff₀ hden]
    linarith [Real.exp_pos (-beta)]
  have hRusso : ∑ e : G.edgeSet,
      FK.activeBCCov G C (FK.betaParams J beta) q f (Lindeberg.coord e) ≤
      deriv (fun b => FK.activeBCMean G C (FK.betaParams J b) q f) beta := by
    rw [hderivEq]
    simpa using StatMech.OSSS.RussoPrefactor.rp_prefactor_extraction
      (fun e : G.edgeSet => J e.1 / (1 - Real.exp (-(beta * J e.1))))
      (fun e => FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e)) 1 hpref hcov0
  have hmain := hcov.trans (by
    simpa [StatMech.OSSS.ActiveBoundaryDifferential.cov_activeBC_eq] using hRusso)
  have hn0 : n ≠ 0 := by omega
  simpa [hexagonalOuterInnerTheta, hexagonalOuterInnerThetaPrime,
    hn0, G, C, J, mu, f] using hmain

noncomputable def hexagonalInnerKappa (n : Nat) (beta0 : Real) : Real :=
  (reindexedOpenIncidentEdges
    (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n))
    (hexagonalBoxEndU n) (hexagonalBoxEndV n) (hexagonalBoxRoot n)).prod
      (fun _ => Real.exp (-beta0))

def hexagonalBoxNeighbor (n : Nat) (hn : 1 ≤ n) (i : Fin 3) :
    HexagonalBoxVertex n :=
  ⟨hexagonalNeighbor (0, false) i, ⟨by
    fin_cases i <;> intro j <;> fin_cases j <;>
      simp [hexagonalNeighbor, hexagonalStep] <;> omega,
    Set.mem_univ _⟩⟩

theorem hexagonalBox_root_neighbor_card_le_six (n : Nat) (hn : 1 ≤ n) :
    ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).card ≤ 6 := by
  let candidates : Finset (HexagonalBoxVertex n) :=
    Finset.univ.image (hexagonalBoxNeighbor n hn)
  have hsub : (hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n) ⊆
      candidates := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    have hyAmbient : hexagonalGraph.Adj (0, false) y.1 := by
      simpa [hexagonalBoxGraph, hexagonalBoxRoot] using hy
    have hc := hexagonal_mem_candidates_of_adj hyAmbient
    rw [Finset.mem_image] at hc ⊢
    obtain ⟨ib, hib, hiy⟩ := hc
    exact ⟨ib, Finset.mem_univ _,
      Subtype.ext (by simpa [hexagonalBoxNeighbor] using hiy)⟩
  calc
    ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).card ≤
        candidates.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_image_le
    _ ≤ 6 := by decide

theorem hexagonalBox_root_degree_le_six (n : Nat) (hn : 1 ≤ n) :
    (hexagonalBoxGraph n).degree (hexagonalBoxRoot n) ≤ 6 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact hexagonalBox_root_neighbor_card_le_six n hn

theorem hexagonalInnerIncident_card_le_six (n : Nat) (hn : 1 ≤ n) :
    (reindexedOpenIncidentEdges
      (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n))
      (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (hexagonalBoxRoot n)).card ≤ 6 := by
  let I := openIncidentEdges (hexagonalBoxEndU n) (hexagonalBoxEndV n)
    (hexagonalBoxRoot n)
  have himage : (reindexedOpenIncidentEdges
      (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n))
      (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (hexagonalBoxRoot n)).card ≤ I.card := by
    unfold reindexedOpenIncidentEdges
    exact Finset.card_image_le
  have hsub : I.image (fun e => e.1) ⊆
      (hexagonalBoxGraph n).incidenceFinset (hexagonalBoxRoot n) := by
    intro edge hedge
    rw [Finset.mem_image] at hedge
    obtain ⟨e, heI, rfl⟩ := hedge
    rw [SimpleGraph.mem_incidenceFinset]
    refine ⟨e.2, ?_⟩
    have heo := (Finset.mem_filter.mp heI).2
    rw [hexagonalBox_end_coherent n e]
    rcases heo with heo | heo
    · simp [heo]
    · simp [heo]
  have hI : I.card ≤
      ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).card := by
    have hincEq : (hexagonalBoxGraph n).incidenceFinset (hexagonalBoxRoot n) =
        ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).image
          (fun w => s(hexagonalBoxRoot n, w)) := by
      ext edge
      induction edge using Sym2.inductionOn with
      | _ a b =>
          simp only [SimpleGraph.mem_incidenceFinset,
            SimpleGraph.mk'_mem_incidenceSet_iff, Finset.mem_image,
            SimpleGraph.mem_neighborFinset]
          constructor
          · rintro ⟨hab, rfl | rfl⟩
            · exact ⟨b, hab, rfl⟩
            · exact ⟨a, hab.symm, Sym2.eq_swap⟩
          · rintro ⟨w, hw, heq⟩
            rcases Sym2.eq_iff.mp heq with ⟨hra, hwb⟩ | ⟨hrb, hwa⟩
            · subst a
              subst b
              exact ⟨hw, by simp⟩
            · subst b
              subst a
              exact ⟨hw.symm, by simp⟩
    have hinj : Set.InjOn (fun w : HexagonalBoxVertex n =>
        s(hexagonalBoxRoot n, w))
        ↑((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)) := by
      intro a ha b hb hab
      rcases Sym2.eq_iff.mp hab with hab | hab
      · exact hab.2
      · exact hab.2.trans hab.1
    calc
      I.card = (I.image (fun e => e.1)).card := by
        symm
        exact Finset.card_image_of_injective I Subtype.val_injective
      _ ≤ ((hexagonalBoxGraph n).incidenceFinset (hexagonalBoxRoot n)).card :=
        Finset.card_le_card hsub
      _ = ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).card := by
        rw [hincEq]
        exact Finset.card_image_of_injOn hinj
  exact himage.trans (hI.trans (hexagonalBox_root_neighbor_card_le_six n hn))

theorem hexagonalInnerKappa_pos (n : Nat) (beta0 : Real) :
    0 < hexagonalInnerKappa n beta0 := by
  unfold hexagonalInnerKappa
  exact Finset.prod_pos fun e he => Real.exp_pos _

theorem exp_neg_pow_six_le_hexagonalInnerKappa
    (n : Nat) (hn : 1 ≤ n) (beta0 : Real) (hbeta0 : 0 ≤ beta0) :
    Real.exp (-beta0) ^ 6 ≤ hexagonalInnerKappa n beta0 := by
  unfold hexagonalInnerKappa
  rw [Finset.prod_const]
  exact pow_le_pow_of_le_one (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by linarith))
    (hexagonalInnerIncident_card_le_six n hn)

theorem hexagonal_outer_inner_one_sub_lower
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    hexagonalInnerKappa n beta0 ≤
      1 - hexagonalOuterInnerTheta q beta n := by
  have hroot : hexagonalBoxRoot n ∉
      (hexagonalBoxShell n n : Set (HexagonalBoxVertex n)) := by
    intro h
    have hnot := (Finset.mem_filter.mp h).2.2
    exact hnot (by
      intro i
      simp [hexagonalBoxRoot])
  have hmain := activeBC_reindexed_openCross_one_sub_lower
    (I := (hexagonalBoxGraph n).edgeSet)
    (hexagonalBoxGraph (2 * n)) (hexagonalBoxBoundaryGraph (2 * n))
    (fun _ => 1) (fun _ => by norm_num) q beta beta0 hq hbeta hbeta0
    (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n))
    (hexagonalBoxEndU n) (hexagonalBoxEndV n) (hexagonalBoxRoot n)
    (hexagonalBoxShell n n : Set (HexagonalBoxVertex n)) hroot
  have hn0 : n ≠ 0 := by omega
  simpa [hexagonalInnerKappa, hexagonalOuterInnerTheta, hn0] using hmain

theorem hexagonal_outer_inner_differential_linear_of_strict_comparison
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0)
    (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      hexagonalOuterCenteredConn n q beta x k ≤
        hexagonalOuterInnerTheta q beta k) :
    hexagonalInnerKappa n beta0 *
        (hexagonalOuterInnerTheta q beta n /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real))) ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  have htheta0 := hexagonalOuterInnerTheta_nonneg q beta hq hbeta n
  have hDpos : 0 < 8 * hexagonalOuterInnerSig n q beta / (n : Real) := by
    have hthetaZero : hexagonalOuterInnerTheta q beta 0 = 1 :=
      hexagonalOuterInnerTheta_zero q beta
    have hsig : 0 < hexagonalOuterInnerSig n q beta := by
      unfold hexagonalOuterInnerSig
      have hsingle : hexagonalOuterInnerTheta q beta 0 ≤
          ∑ k ∈ Finset.range n, hexagonalOuterInnerTheta q beta k := by
        apply Finset.single_le_sum
          (fun k _ => hexagonalOuterInnerTheta_nonneg q beta hq hbeta k)
        simpa using hn
      linarith
    have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hgap := hexagonal_outer_inner_one_sub_lower
    n hn q beta beta0 hq hbeta hbeta0
  have hlog := hexagonal_outer_inner_differential_sharp_of_strict_comparison
    n hn q beta hq hbeta hcomp
  calc
    hexagonalInnerKappa n beta0 *
        (hexagonalOuterInnerTheta q beta n /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real))) =
      hexagonalOuterInnerTheta q beta n * hexagonalInnerKappa n beta0 /
        (8 * hexagonalOuterInnerSig n q beta / (n : Real)) := by ring
    _ ≤ hexagonalOuterInnerTheta q beta n *
        (1 - hexagonalOuterInnerTheta q beta n) /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real)) :=
      (div_le_div_iff_of_pos_right hDpos).2
        (mul_le_mul_of_nonneg_left hgap htheta0)
    _ ≤ hexagonalOuterInnerThetaPrime n q beta := hlog

theorem hexagonal_outer_inner_hcov_sharp
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (hexagonalInnerCrossInd n) *
        (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤
      ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
  apply hexagonal_outer_inner_hcov_sharp_of_strict_comparison
    n hn q beta hq hbeta
  intro x k hk hstrict
  exact hexagonalOuterCenteredConn_le_theta_strict n k x
    (Finset.mem_Icc.mp hk).1 hstrict q beta hq hbeta

theorem hexagonal_outer_inner_differential_sharp
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonalOuterInnerTheta q beta n *
        (1 - hexagonalOuterInnerTheta q beta n) /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  apply hexagonal_outer_inner_differential_sharp_of_strict_comparison
    n hn q beta hq hbeta
  intro x k hk hstrict
  exact hexagonalOuterCenteredConn_le_theta_strict n k x
    (Finset.mem_Icc.mp hk).1 hstrict q beta hq hbeta

theorem hexagonal_outer_inner_differential_linear
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    hexagonalInnerKappa n beta0 *
        (hexagonalOuterInnerTheta q beta n /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real))) ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  apply hexagonal_outer_inner_differential_linear_of_strict_comparison
    n hn q beta beta0 hq hbeta hbeta0
  intro x k hk hstrict
  exact hexagonalOuterCenteredConn_le_theta_strict n k x
    (Finset.mem_Icc.mp hk).1 hstrict q beta hq hbeta

theorem hexagonalOuterInnerSig_pos
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    0 < hexagonalOuterInnerSig n q beta := by
  have hsingle : hexagonalOuterInnerTheta q beta 0 ≤
      ∑ k ∈ Finset.range n, hexagonalOuterInnerTheta q beta k := by
    apply Finset.single_le_sum
      (fun k _ => hexagonalOuterInnerTheta_nonneg q beta hq hbeta k)
    simpa using hn
  rw [hexagonalOuterInnerTheta_zero] at hsingle
  exact lt_of_lt_of_le zero_lt_one hsingle

noncomputable def hexagonalSharpConstant (beta0 : Real) : Real :=
  Real.exp (-beta0) ^ 6 / 8

theorem hexagonalSharpConstant_pos (beta0 : Real) :
    0 < hexagonalSharpConstant beta0 := by
  unfold hexagonalSharpConstant
  positivity

theorem hexagonal_outer_inner_differential_uniform
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    hexagonalSharpConstant beta0 *
        (((n : Real) / hexagonalOuterInnerSig n q beta) *
          hexagonalOuterInnerTheta q beta n) ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  have hbeta0nonneg : 0 ≤ beta0 := hbeta.le.trans hbeta0
  have hkappa := exp_neg_pow_six_le_hexagonalInnerKappa
    n hn beta0 hbeta0nonneg
  have hmain := hexagonal_outer_inner_differential_linear
    n hn q beta beta0 hq hbeta hbeta0
  have htheta0 := hexagonalOuterInnerTheta_nonneg q beta hq hbeta n
  have hsig := hexagonalOuterInnerSig_pos n hn q beta hq hbeta
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    hexagonalSharpConstant beta0 *
        (((n : Real) / hexagonalOuterInnerSig n q beta) *
          hexagonalOuterInnerTheta q beta n) ≤
      (hexagonalInnerKappa n beta0 / 8) *
        (((n : Real) / hexagonalOuterInnerSig n q beta) *
          hexagonalOuterInnerTheta q beta n) := by
        apply mul_le_mul_of_nonneg_right
        · exact div_le_div_of_nonneg_right hkappa (by norm_num)
        · positivity
    _ = hexagonalInnerKappa n beta0 *
        (hexagonalOuterInnerTheta q beta n /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real))) := by
      field_simp
    _ ≤ hexagonalOuterInnerThetaPrime n q beta := hmain

end StatMech.FK.PeriodicPlanar
