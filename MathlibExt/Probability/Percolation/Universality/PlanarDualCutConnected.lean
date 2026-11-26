/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.DualCutToPath

/-!
# The primal barrier graph and the rotated cut hypothesis

The *primal barrier graph* of `rect 0 n 0 n` has the barrier edges (in-square edges from the
left-reach set to its complement) as its edges. The rotated barrier graph `dcw_dualBarrierGraph` is
its image under the quarter turn `rot90Fun` (`pdc_rot90Iso`). Under this isomorphism the rotated
cut hypothesis `dcp_DualCutConnectsRot ω n` (bottom and top sides of `rect (-n) 0 0 n` joined in
the rotated barrier graph) is equivalent to the left and right sides of `rect 0 n 0 n` being
joined in the primal barrier graph (`pdc_primalConnects_iff_DualCutConnectsRot`).

Barrier edges are joined in these graphs only through shared endpoints, which is not how
consecutive edges of a dual circuit meet (they meet at faces). Accordingly the cut hypothesis does
not follow from the absence of a horizontal crossing: in the all-closed configuration with
`n ≥ 2` the barrier edges `{(0,y),(1,y)}` are pairwise disjoint and never reach the right side
(`pdc_allClosed_not_DualCutConnectsRot`).

## Main definitions

* `StatMech.Universality.pdc_barrierGraphPrimal`: the graph of barrier edges.
* `StatMech.Universality.pdc_rot90Iso`: the quarter turn as a graph isomorphism onto the rotated
  barrier graph.
* `StatMech.Universality.pdc_PrimalBarrierConnects`: the left and right sides are joined in the
  primal barrier graph.

## Main results

* `StatMech.Universality.pdc_primalConnects_iff_DualCutConnectsRot`: the primal and rotated
  connection hypotheses are equivalent.
* `StatMech.Universality.pdc_rotatedDualVerticalCrossing_of_primalConnects`: a primal barrier
  connection gives a vertical crossing of `rect (-n) 0 0 n` in `dualConfig ω`.
* `StatMech.Universality.pdc_allClosed_not_DualCutConnectsRot`: for `n ≥ 2` the all-closed
  configuration has no horizontal crossing (`pdc_allClosed_noH`) and does not satisfy the rotated
  cut hypothesis.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}

/-- The primal barrier graph of `rect 0 n 0 n`: `a` and `b` are adjacent when `{a, b}` is a
barrier edge. -/
def pdc_barrierGraphPrimal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    SimpleGraph (Site 2) where
  Adj a b :=
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧
      ((a = v ∧ b = w) ∨ (a = w ∧ b = v))
  symm := by
    refine ⟨?_⟩
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

/-- The quarter turn maps primal barrier edges to rotated barrier edges. -/
theorem pdc_rot90_adj_dual (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {a b : Site 2}
    (h : (pdc_barrierGraphPrimal ω n).Adj a b) :
    (dcw_dualBarrierGraph ω n).Adj (rot90Fun a) (rot90Fun b) := by
  obtain ⟨v, w, hvw, hab⟩ := h
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨v, w, hvw, Or.inl ⟨by rw [ha], by rw [hb]⟩⟩
  · exact ⟨v, w, hvw, Or.inr ⟨by rw [ha], by rw [hb]⟩⟩

/-- The quarter turn as a graph homomorphism from the primal to the rotated barrier graph. -/
def pdc_rot90Hom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    pdc_barrierGraphPrimal ω n →g dcw_dualBarrierGraph ω n where
  toFun := rot90Fun
  map_rel' := fun h => pdc_rot90_adj_dual ω n h

@[simp] theorem pdc_rot90Hom_apply (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (a : Site 2) :
    pdc_rot90Hom ω n a = rot90Fun a := rfl

/-- The inverse quarter turn maps rotated barrier edges to primal barrier edges. -/
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

/-- The inverse quarter turn as a graph homomorphism from the rotated to the primal barrier
graph. -/
def pdc_rot90InvHom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    dcw_dualBarrierGraph ω n →g pdc_barrierGraphPrimal ω n where
  toFun := rot90Inv
  map_rel' := fun h => pdc_rot90Inv_adj_primal ω n h

@[simp] theorem pdc_rot90InvHom_apply (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (p : Site 2) :
    pdc_rot90InvHom ω n p = rot90Inv p := rfl

/-- The quarter turn is a graph isomorphism from the primal barrier graph onto the rotated
barrier graph `dcw_dualBarrierGraph ω n`. -/
def pdc_rot90Iso (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    pdc_barrierGraphPrimal ω n ≃g dcw_dualBarrierGraph ω n where
  toEquiv := rot90Equiv
  map_rel_iff' {a b} := by
    refine ⟨fun h => ?_, fun h => pdc_rot90_adj_dual ω n h⟩
    have := pdc_rot90Inv_adj_primal ω n h
    rwa [rot90Equiv_apply, rot90Equiv_apply, show rot90Inv (rot90Fun a) = a from
      rot90Equiv.left_inv a, show rot90Inv (rot90Fun b) = b from rot90Equiv.left_inv b] at this

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
    rwa [show rot90Inv (rot90Fun a) = a from rot90Equiv.left_inv a,
      show rot90Inv (rot90Fun b) = b from rot90Equiv.left_inv b] at this
  · exact pdc_dualReach_of_primalReach ω n

/-- Some left-side site of `rect 0 n 0 n` is joined to some right-side site in the primal barrier
graph. -/
def pdc_PrimalBarrierConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (a : Site 2) (_ha : a ∈ leftSide 0 n 0 n)
    (b : Site 2) (_hb : b ∈ rightSide 0 n 0 n),
    (pdc_barrierGraphPrimal ω n).Reachable a b

theorem pdc_DualCutConnectsRot_of_primalConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pdc_PrimalBarrierConnects ω n) : dcp_DualCutConnectsRot ω n := by
  obtain ⟨a, ha, b, hb, hreach⟩ := h
  refine ⟨rot90Fun a, dcp_rot90_leftSide n ha, rot90Fun b, dcp_rot90_rightSide n hb, ?_⟩
  exact pdc_dualReach_of_primalReach ω n hreach

/-- A primal barrier connection gives a vertical crossing of the rotated square
`rect (-n) 0 0 n` in `dualConfig ω`. -/
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

/-- The quarter turn of a primal barrier walk, as a rotated barrier walk. -/
def pdc_dualBarrier_walk_of_primalWalk (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {a b : Site 2} (c : (pdc_barrierGraphPrimal ω n).Walk a b) :
    (dcw_dualBarrierGraph ω n).Walk (rot90Fun a) (rot90Fun b) :=
  c.map (pdc_rot90Hom ω n)

theorem pdc_dualWalk_endpoints (_ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
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

/-- Two barrier edges with the same inner endpoint are joined in the primal barrier graph. -/
theorem pdc_share_at_inside (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w₁ w₂ : Site 2}
    (hbar₁ : dcw_isBarrierEdge ω n v w₁) (hbar₂ : dcw_isBarrierEdge ω n v w₂) :
    (pdc_barrierGraphPrimal ω n).Reachable w₁ w₂ := by
  have h1 : (pdc_barrierGraphPrimal ω n).Adj w₁ v := ⟨v, w₁, hbar₁, Or.inr ⟨rfl, rfl⟩⟩
  have h2 : (pdc_barrierGraphPrimal ω n).Adj v w₂ := ⟨v, w₂, hbar₂, Or.inl ⟨rfl, rfl⟩⟩
  exact h1.reachable.trans h2.reachable

/-- Two barrier edges with the same outer endpoint are joined in the primal barrier graph. -/
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

/-- In the all-closed configuration the left-reach set lies in the column `x = 0`. See also
`bcc_leftReach_bot_eq`. -/
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

/-- For `n ≥ 1` the all-closed configuration has no open horizontal crossing. -/
theorem pdc_allClosed_noH (n : ℤ) (hn : 1 ≤ n) :
    ¬ HorizontalCrossing (fun _ => false) 0 n 0 n := by
  rw [bcd_no_horizontal_iff_right_unreachable]
  intro y hy hyL
  have h0 := pdc_allClosed_leftReach_x0 n hyL
  have hyn : y 0 = n := hy.2
  omega

/-- For `n ≥ 2`, in the all-closed configuration the right-side sites are isolated in the primal
barrier graph. -/
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

/-- For `n ≥ 2` the all-closed configuration, which has no horizontal crossing
(`pdc_allClosed_noH`), does not satisfy `dcp_DualCutConnectsRot`. So the rotated cut hypothesis
is not implied by the absence of a horizontal crossing. -/
theorem pdc_allClosed_not_DualCutConnectsRot (n : ℤ) (hn : 2 ≤ n) :
    ¬ dcp_DualCutConnectsRot (fun _ => false) n := by
  intro h
  exact pdc_allClosed_not_primalConnects n hn
    (pdc_primalConnects_of_DualCutConnectsRot (fun _ => false) n h)

end Universality

end StatMech
