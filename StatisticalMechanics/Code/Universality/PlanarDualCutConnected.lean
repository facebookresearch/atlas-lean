/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.RSW.Defs
import Code.RSW.SelfDuality
import Code.Lattice.CrossingParity
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.FaceRegion
import Code.Lattice.JordanContour
import Code.Universality.BoxCrossingDichotomy
import Code.Universality.DualCircuitToWalk
import Code.Universality.DualCutToPath

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}













def pdc_barrierGraphPrimal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    SimpleGraph (Site 2) where
  Adj a b :=
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧
      ((a = v ∧ b = w) ∨ (a = w ∧ b = v))
  symm := by
    rintro a b ⟨v, w, hvw, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩
    · exact ⟨v, w, hvw, Or.inr ⟨hb, ha⟩⟩
    · exact ⟨v, w, hvw, Or.inl ⟨hb, ha⟩⟩
  loopless := by
    refine ⟨fun a ha => ?_⟩
    rcases ha with ⟨v, w, hvw, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩
    · rw [ha] at hb
      exact (hypercubicLattice 2).ne_of_adj hvw.2.2.2 hb
    · rw [ha] at hb
      exact (hypercubicLattice 2).ne_of_adj hvw.2.2.2 hb.symm

@[simp] theorem pdc_barrierGraphPrimal_adj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (a b : Site 2) :
    (pdc_barrierGraphPrimal ω n).Adj a b ↔
      ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧
        ((a = v ∧ b = w) ∨ (a = w ∧ b = v)) := Iff.rfl



theorem pdc_rot90_adj_dual (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {a b : Site 2}
    (h : (pdc_barrierGraphPrimal ω n).Adj a b) :
    (dcw_dualBarrierGraph ω n).Adj (rot90Fun a) (rot90Fun b) := by
  obtain ⟨v, w, hvw, hab⟩ := h
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨v, w, hvw, Or.inl ⟨by rw [ha], by rw [hb]⟩⟩
  · exact ⟨v, w, hvw, Or.inr ⟨by rw [ha], by rw [hb]⟩⟩




def pdc_rot90Hom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    pdc_barrierGraphPrimal ω n →g dcw_dualBarrierGraph ω n where
  toFun := rot90Fun
  map_rel' := fun {a b} h => pdc_rot90_adj_dual ω n h

@[simp] theorem pdc_rot90Hom_apply (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (a : Site 2) :
    pdc_rot90Hom ω n a = rot90Fun a := rfl




theorem pdc_rot90Inv_adj_primal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {p q : Site 2}
    (h : (dcw_dualBarrierGraph ω n).Adj p q) :
    (pdc_barrierGraphPrimal ω n).Adj (rot90Inv p) (rot90Inv q) := by
  obtain ⟨v, w, hvw, hpq⟩ := h
  have hinvrot : ∀ x : Site 2, rot90Inv (rot90Fun x) = x := fun x => rot90Equiv.left_inv x
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · refine ⟨v, w, hvw, Or.inl ⟨?_, ?_⟩⟩
    · rw [hp, hinvrot]
    · rw [hq, hinvrot]
  · refine ⟨v, w, hvw, Or.inr ⟨?_, ?_⟩⟩
    · rw [hp, hinvrot]
    · rw [hq, hinvrot]



def pdc_rot90InvHom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    dcw_dualBarrierGraph ω n →g pdc_barrierGraphPrimal ω n where
  toFun := rot90Inv
  map_rel' := fun {p q} h => pdc_rot90Inv_adj_primal ω n h

@[simp] theorem pdc_rot90InvHom_apply (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (p : Site 2) :
    pdc_rot90InvHom ω n p = rot90Inv p := rfl









theorem pdc_rot90Inv_rot90Fun (x : Site 2) : rot90Inv (rot90Fun x) = x := by
  funext i; fin_cases i <;> simp [rot90Fun, rot90Inv]



theorem pdc_dualReach_of_primalReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {a b : Site 2} (h : (pdc_barrierGraphPrimal ω n).Reachable a b) :
    (dcw_dualBarrierGraph ω n).Reachable (rot90Fun a) (rot90Fun b) := by
  have := h.map (pdc_rot90Hom ω n)
  simpa using this



theorem pdc_primalReach_of_dualReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (h : (dcw_dualBarrierGraph ω n).Reachable p q) :
    (pdc_barrierGraphPrimal ω n).Reachable (rot90Inv p) (rot90Inv q) := by
  have := h.map (pdc_rot90InvHom ω n)
  simpa using this





theorem pdc_dualReach_iff_primalReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (a b : Site 2) :
    (dcw_dualBarrierGraph ω n).Reachable (rot90Fun a) (rot90Fun b) ↔
      (pdc_barrierGraphPrimal ω n).Reachable a b := by
  constructor
  · intro h
    have := pdc_primalReach_of_dualReach ω n h
    rwa [pdc_rot90Inv_rot90Fun a, pdc_rot90Inv_rot90Fun b] at this
  · exact pdc_dualReach_of_primalReach ω n

















def pdc_PrimalBarrierConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (a : Site 2) (_ha : a ∈ leftSide 0 n 0 n)
    (b : Site 2) (_hb : b ∈ rightSide 0 n 0 n),
    (pdc_barrierGraphPrimal ω n).Reachable a b





theorem pdc_DualCutConnectsRot_of_primalConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pdc_PrimalBarrierConnects ω n) : dcp_DualCutConnectsRot ω n := by
  obtain ⟨a, ha, b, hb, hreach⟩ := h
  refine ⟨rot90Fun a, dcp_rot90_leftSide n ha, rot90Fun b, dcp_rot90_rightSide n hb, ?_⟩
  exact pdc_dualReach_of_primalReach ω n hreach





theorem pdc_rotatedDualVerticalCrossing_of_primalConnects
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pdc_PrimalBarrierConnects ω n) :
    DualVerticalCrossing ω (-n) 0 0 n :=
  dcp_rotatedDualVerticalCrossing_of_cutConnectsRot ω n
    (pdc_DualCutConnectsRot_of_primalConnects ω n h)











theorem pdc_bottomBarrierEdge_primal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v w : Site 2, (pdc_barrierGraphPrimal ω n).Adj v w ∧ v 1 = 0 ∧ w 1 = 0 := by
  obtain ⟨v, w, hbar, hv0, hw0⟩ := dcw_barrierEdge_exists ω n hn hnoH
  exact ⟨v, w, ⟨v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩, hv0, hw0⟩




theorem pdc_topBarrierEdge_primal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v w : Site 2, (pdc_barrierGraphPrimal ω n).Adj v w ∧ v 1 = n ∧ w 1 = n := by
  obtain ⟨v, w, hbar, hvn, hwn⟩ := dcp_topBarrierEdge_exists ω n hn hnoH
  exact ⟨v, w, ⟨v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩, hvn, hwn⟩




theorem pdc_primalBarrier_nonempty_edge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ a b : Site 2, (pdc_barrierGraphPrimal ω n).Adj a b := by
  obtain ⟨v, w, hadj, _, _⟩ := pdc_bottomBarrierEdge_primal ω n hn hnoH
  exact ⟨v, w, hadj⟩









def pdc_dualBarrier_walk_of_primalWalk (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {a b : Site 2} (c : (pdc_barrierGraphPrimal ω n).Walk a b) :
    (dcw_dualBarrierGraph ω n).Walk (rot90Fun a) (rot90Fun b) :=
  c.map (pdc_rot90Hom ω n)





theorem pdc_dualWalk_endpoints (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {a b : Site 2} (ha : a ∈ leftSide 0 n 0 n) (hb : b ∈ rightSide 0 n 0 n) :
    rot90Fun a ∈ bottomSide (-n) 0 0 n ∧ rot90Fun b ∈ topSide (-n) 0 0 n :=
  ⟨dcp_rot90_leftSide n ha, dcp_rot90_rightSide n hb⟩












theorem pdc_rot90Inv_bottomSide (n : ℤ) {p : Site 2} (hp : p ∈ bottomSide (-n) 0 0 n) :
    rot90Inv p ∈ leftSide 0 n 0 n := by
  obtain ⟨hbox, h0⟩ := hp
  rw [mem_rect] at hbox
  refine ⟨?_, ?_⟩
  · rw [mem_rect, rot90Inv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [rot90Inv]; simp [h0]



theorem pdc_rot90Inv_topSide (n : ℤ) {q : Site 2} (hq : q ∈ topSide (-n) 0 0 n) :
    rot90Inv q ∈ rightSide 0 n 0 n := by
  obtain ⟨hbox, h0⟩ := hq
  rw [mem_rect] at hbox
  refine ⟨?_, ?_⟩
  · rw [mem_rect, rot90Inv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [rot90Inv]; simp [h0]





theorem pdc_primalConnects_of_DualCutConnectsRot (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : dcp_DualCutConnectsRot ω n) : pdc_PrimalBarrierConnects ω n := by
  obtain ⟨p₀, hp₀, q₀, hq₀, hreach⟩ := h
  refine ⟨rot90Inv p₀, pdc_rot90Inv_bottomSide n hp₀,
    rot90Inv q₀, pdc_rot90Inv_topSide n hq₀, ?_⟩
  exact pdc_primalReach_of_dualReach ω n hreach





theorem pdc_primalConnects_iff_DualCutConnectsRot (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    pdc_PrimalBarrierConnects ω n ↔ dcp_DualCutConnectsRot ω n :=
  ⟨pdc_DualCutConnectsRot_of_primalConnects ω n,
    pdc_primalConnects_of_DualCutConnectsRot ω n⟩
















theorem pdc_share_at_inside (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w₁ w₂ : Site 2}
    (hbar₁ : dcw_isBarrierEdge ω n v w₁) (hbar₂ : dcw_isBarrierEdge ω n v w₂) :
    (pdc_barrierGraphPrimal ω n).Reachable w₁ w₂ := by
  have h1 : (pdc_barrierGraphPrimal ω n).Adj w₁ v := ⟨v, w₁, hbar₁, Or.inr ⟨rfl, rfl⟩⟩
  have h2 : (pdc_barrierGraphPrimal ω n).Adj v w₂ := ⟨v, w₂, hbar₂, Or.inl ⟨rfl, rfl⟩⟩
  exact h1.reachable.trans h2.reachable





theorem pdc_share_at_outside (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v₁ v₂ w : Site 2}
    (hbar₁ : dcw_isBarrierEdge ω n v₁ w) (hbar₂ : dcw_isBarrierEdge ω n v₂ w) :
    (pdc_barrierGraphPrimal ω n).Reachable v₁ v₂ := by
  have h1 : (pdc_barrierGraphPrimal ω n).Adj v₁ w := ⟨v₁, w, hbar₁, Or.inl ⟨rfl, rfl⟩⟩
  have h2 : (pdc_barrierGraphPrimal ω n).Adj w v₂ := ⟨v₂, w, hbar₂, Or.inr ⟨rfl, rfl⟩⟩
  exact h1.reachable.trans h2.reachable




theorem pdc_barrierEdge_reachable (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (hbar : dcw_isBarrierEdge ω n v w) :
    (pdc_barrierGraphPrimal ω n).Reachable v w :=
  (show (pdc_barrierGraphPrimal ω n).Adj v w from ⟨v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩).reachable


































theorem pdc_allClosed_leftReach_x0 (n : ℤ) {v : Site 2}
    (hv : v ∈ bcd_leftReach (fun _ => false) n) : v 0 = 0 := by
  obtain ⟨_hvbox, x, hxL, hvbox', hconn⟩ := hv
  have hxv : (⟨x, leftSide_subset hxL⟩ : (rect 0 n 0 n)) = ⟨v, hvbox'⟩ := by
    obtain ⟨w⟩ := hconn
    cases w with
    | nil => rfl
    | cons hadj _ =>
        exfalso
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hadj; simp at hadj
  have hxveq : x = v := by have := congrArg Subtype.val hxv; simpa using this
  rw [← hxveq]; exact hxL.2



theorem pdc_allClosed_noH (n : ℤ) (hn : 1 ≤ n) :
    ¬ HorizontalCrossing (fun _ => false) 0 n 0 n := by
  rw [bcd_no_horizontal_iff_right_unreachable]
  intro y hy hyL
  have h0 := pdc_allClosed_leftReach_x0 n hyL
  have hyn : y 0 = n := hy.2
  omega





theorem pdc_allClosed_rightSide_isolated (n : ℤ) (hn : 2 ≤ n) {b : Site 2}
    (hb : b ∈ rightSide 0 n 0 n) (z : Site 2) :
    ¬ (pdc_barrierGraphPrimal (fun _ => false) n).Adj b z := by
  have hbn : b 0 = n := hb.2
  rintro ⟨v, w, hvw, (⟨ha, _⟩ | ⟨ha, _⟩)⟩
  · subst ha; have := pdc_allClosed_leftReach_x0 n hvw.1; omega
  · subst ha
    have hz0 : v 0 = 0 := pdc_allClosed_leftReach_x0 n hvw.1
    have hadj := hvw.2.2.2
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    have h1 : (v 0 - b 0).natAbs = n.natAbs := by rw [hz0, hbn]; simp
    omega






theorem pdc_allClosed_not_primalConnects (n : ℤ) (hn : 2 ≤ n) :
    ¬ pdc_PrimalBarrierConnects (fun _ => false) n := by
  rintro ⟨a, ha, b, hb, hreach⟩
  have hab : a = b := by
    obtain ⟨w⟩ := hreach.symm
    cases w with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (pdc_allClosed_rightSide_isolated n hn hb _)
  subst hab
  have h0 : a 0 = 0 := ha.2
  have hn' : a 0 = n := hb.2
  omega







theorem pdc_allClosed_not_DualCutConnectsRot (n : ℤ) (hn : 2 ≤ n) :
    ¬ dcp_DualCutConnectsRot (fun _ => false) n := by
  intro h
  exact pdc_allClosed_not_primalConnects n hn
    (pdc_primalConnects_of_DualCutConnectsRot (fun _ => false) n h)

end Universality

end StatMech
