/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.BeffaraDC.TorusCellComplement
import Code.BeffaraDC.TorusConnected
import Code.Lattice.JordanEnclosure
import Code.Lattice.EulerComponentCount










open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Lattice
open StatMech.Onsager


def torusCellEdgeStraddles {V : Type*} (S : Set V) (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun x y => (x ∈ S ↔ y ∉ S), by
    intro x y
    simp only [eq_iff_iff]
    tauto⟩ e

@[simp] theorem torusCellEdgeStraddles_mk {V : Type*} (S : Set V) (x y : V) :
    torusCellEdgeStraddles S s(x, y) ↔ (x ∈ S ↔ y ∉ S) := Iff.rfl


noncomputable def torusCellCutDualGraph (L : ℕ) [Fact (2 < L)]
    (S : Set (ZMod L × ZMod L)) : SimpleGraph (ZMod L × ZMod L) where
  Adj f g := (onsTorusGraph L).Adj f g ∧
    torusCellEdgeStraddles S (torusCellPrimalOfDualEdge L s(f, g))
  symm := by
    rintro f g ⟨hfg, hcut⟩
    refine ⟨hfg.symm, ?_⟩
    simpa [Sym2.eq_swap] using hcut
  loopless := ⟨fun f h => (onsTorusGraph L).irrefl h.1⟩

@[simp] theorem torusCellCutDualGraph_adj (L : ℕ) [Fact (2 < L)]
    (S : Set (ZMod L × ZMod L)) (f g : ZMod L × ZMod L) :
    (torusCellCutDualGraph L S).Adj f g ↔
      (onsTorusGraph L).Adj f g ∧
        torusCellEdgeStraddles S
          (torusCellPrimalOfDualEdge L s(f, g)) := Iff.rfl

noncomputable local instance torusCellCutDualGraph_decidableRel
    (L : ℕ) [Fact (2 < L)] (S : Set (ZMod L × ZMod L)) :
    DecidableRel (torusCellCutDualGraph L S).Adj := Classical.decRel _

@[simp] theorem torusCellPrimalOfDualEdge_horizontal
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    torusCellPrimalOfDualEdge L
      s((x, y), (x + 1, y)) =
        s((x + 1, y), (x + 1, y + 1)) := by
  have he := (torusHorizontalEdge L x y).2
  change torusCellPrimalOfDualEdge L
    (torusHorizontalEdge L x y : Sym2 (ZMod L × ZMod L)) = _
  rw [torusCellPrimalOfDualEdge_of_mem L he]
  change (((torusCellCrossing L).symm
    (torusHorizontalEdge L x y) : TorusAmbientEdge L) :
      Sym2 (ZMod L × ZMod L)) = _
  simp

@[simp] theorem torusCellPrimalOfDualEdge_vertical
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    torusCellPrimalOfDualEdge L
      s((x, y), (x, y + 1)) =
        s((x, y + 1), (x + 1, y + 1)) := by
  have he := (torusVerticalEdge L x y).2
  change torusCellPrimalOfDualEdge L
    (torusVerticalEdge L x y : Sym2 (ZMod L × ZMod L)) = _
  rw [torusCellPrimalOfDualEdge_of_mem L he]
  change (((torusCellCrossing L).symm
    (torusVerticalEdge L x y) : TorusAmbientEdge L) :
      Sym2 (ZMod L × ZMod L)) = _
  simp

@[simp] theorem torusCellPrimalOfDualEdge_down
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    torusCellPrimalOfDualEdge L
      s((x, y), (x, y - 1)) =
        s((x, y), (x + 1, y)) := by
  rw [Sym2.eq_swap]
  convert torusCellPrimalOfDualEdge_vertical L x (y - 1) using 1 <;>
    congr 1 <;> ext <;> simp <;> ring

@[simp] theorem torusCellPrimalOfDualEdge_left
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    torusCellPrimalOfDualEdge L
      s((x, y), (x - 1, y)) =
        s((x, y), (x, y + 1)) := by
  rw [Sym2.eq_swap]
  convert torusCellPrimalOfDualEdge_horizontal L (x - 1) y using 1 <;>
    congr 1 <;> ext <;> simp <;> ring

@[simp] theorem torusCellPrimalOfDualEdge_up
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    torusCellPrimalOfDualEdge L
      s((x, y), (x, y + 1)) =
        s((x, y + 1), (x + 1, y + 1)) :=
  torusCellPrimalOfDualEdge_vertical L x y

@[simp] theorem torusCellPrimalOfDualEdge_right
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    torusCellPrimalOfDualEdge L
      s((x, y), (x + 1, y)) =
        s((x + 1, y), (x + 1, y + 1)) :=
  torusCellPrimalOfDualEdge_horizontal L x y


theorem torusCell_ambient_neighborFinset (L : ℕ) [Fact (2 < L)]
    (v : ZMod L × ZMod L) :
    (onsTorusGraph L).neighborFinset v =
      {(v.1, v.2 - 1), (v.1, v.2 + 1),
        (v.1 - 1, v.2), (v.1 + 1, v.2)} := by
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨g1, g2 | g2⟩ | ⟨g1, g2 | g2⟩)
    · exact Or.inl (Prod.ext_iff.mpr
        ⟨g1.symm, by linear_combination -g2⟩)
    · exact Or.inr (Or.inl (Prod.ext_iff.mpr
        ⟨g1.symm, by linear_combination -g2⟩))
    · exact Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr
        ⟨by linear_combination -g2, g1.symm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Prod.ext_iff.mpr
        ⟨by linear_combination -g2, g1.symm⟩)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl ⟨rfl, Or.inl (by ring)⟩
    · exact Or.inl ⟨rfl, Or.inr (by ring)⟩
    · exact Or.inr ⟨rfl, Or.inl (by ring)⟩
    · exact Or.inr ⟨rfl, Or.inr (by ring)⟩



theorem torusCellCutDualGraph_degree_even (L : ℕ) [Fact (2 < L)]
    (S : Set (ZMod L × ZMod L)) (v : ZMod L × ZMod L) :
    Even ((torusCellCutDualGraph L S).degree v) := by
  classical
  have hfilter : (torusCellCutDualGraph L S).neighborFinset v =
      ((onsTorusGraph L).neighborFinset v).filter (fun w =>
        torusCellEdgeStraddles S
          (torusCellPrimalOfDualEdge L s(v, w))) := by
    ext w
    simp [torusCellCutDualGraph_adj]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hfilter,
    torusCell_ambient_neighborFinset]
  rcases v with ⟨x, y⟩
  have h1 : (1 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_one, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : 2 < L)
    omega
  have h2 : (2 : ZMod L) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod L) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
      have := (Fact.out : 2 < L)
      omega
    simpa using h
  have hAB : (x, y - 1) ≠ (x, y + 1) := by
    intro h
    rw [Prod.ext_iff] at h
    exact h2 (by linear_combination -h.2)
  have hAC : (x, y - 1) ≠ (x - 1, y) := by
    intro h
    rw [Prod.ext_iff] at h
    exact h1 (by linear_combination h.1)
  have hAD : (x, y - 1) ≠ (x + 1, y) := by
    intro h
    rw [Prod.ext_iff] at h
    exact h1 (by linear_combination -h.1)
  have hBC : (x, y + 1) ≠ (x - 1, y) := by
    intro h
    rw [Prod.ext_iff] at h
    exact h1 (by linear_combination h.1)
  have hBD : (x, y + 1) ≠ (x + 1, y) := by
    intro h
    rw [Prod.ext_iff] at h
    exact h1 (by linear_combination -h.1)
  have hCD : (x - 1, y) ≠ (x + 1, y) := by
    intro h
    rw [Prod.ext_iff] at h
    exact h2 (by linear_combination -h.1)
  by_cases h00 : (x, y) ∈ S <;>
  by_cases h10 : (x + 1, y) ∈ S <;>
  by_cases h01 : (x, y + 1) ∈ S <;>
  by_cases h11 : (x + 1, y + 1) ∈ S <;>
    simp only [Finset.filter_insert, Finset.filter_singleton] <;>
    simp [torusCellPrimalOfDualEdge_down,
      torusCellPrimalOfDualEdge_up,
      torusCellPrimalOfDualEdge_left,
      torusCellPrimalOfDualEdge_right, h00, h10, h01, h11,
      hAB, hAC, hAD, hBC, hBD, hCD] <;> norm_num


theorem torusCellPrimalOfDualOfPrimalEdge (L : ℕ) [Fact (2 < L)]
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellPrimalOfDualEdge L (torusCellDualOfPrimalEdge L e) = e := by
  rw [torusCellDualOfPrimalEdge_of_mem L he]
  have hd : ((torusCellCrossing L ⟨e, he⟩ : TorusAmbientEdge L) :
      Sym2 (ZMod L × ZMod L)) ∈ (onsTorusGraph L).edgeFinset :=
    (torusCellCrossing L ⟨e, he⟩).2
  rw [torusCellPrimalOfDualEdge_of_mem L hd]
  exact congrArg Subtype.val ((torusCellCrossing L).symm_apply_apply ⟨e, he⟩)



theorem torusCellCutDualGraph_le_dualCutGraph
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L))
    (S : Set (ZMod L × ZMod L))
    (hclosed : ∀ {u v}, G.Adj u v → (u ∈ S ↔ v ∈ S)) :
    torusCellCutDualGraph L S ≤ torusCellDualCutGraph L G := by
  intro f g hfg
  refine ⟨hfg.1, ?_⟩
  let e := torusCellPrimalOfDualEdge L s(f, g)
  have hcut : torusCellEdgeStraddles S e := hfg.2
  change e ∉ G.edgeSet
  revert hcut
  induction e using Sym2.inductionOn with
  | _ u v =>
      intro hcut
      intro hopen
      rw [SimpleGraph.mem_edgeSet] at hopen
      have hs := hclosed hopen
      simpa [torusCellEdgeStraddles_mk, hs] using hcut




theorem torusCellDualCutGraph_crossed_reachable_of_primal_not_reachable
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) {p q f g : ZMod L × ZMod L}
    (hpq : (onsTorusGraph L).Adj p q)
    (hmerge : ¬ G.Reachable p q)
    (hdual : torusCellDualOfPrimalEdge L s(p, q) = s(f, g)) :
    ((torusCellDualCutGraph L G).deleteEdges {s(f, g)}).Reachable f g := by
  classical
  let S : Set (ZMod L × ZMod L) := {z | G.Reachable p z}
  let B := torusCellCutDualGraph L S
  have hclosed : ∀ {u v}, G.Adj u v → (u ∈ S ↔ v ∈ S) := by
    intro u v huv
    change G.Reachable p u ↔ G.Reachable p v
    exact ⟨fun h => h.trans huv.reachable,
      fun h => h.trans huv.symm.reachable⟩
  have hle : B ≤ torusCellDualCutGraph L G :=
    torusCellCutDualGraph_le_dualCutGraph L G S hclosed
  have hePrimal : s(p, q) ∈ (onsTorusGraph L).edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset] using hpq
  have heDual : s(f, g) ∈ (onsTorusGraph L).edgeFinset := by
    rw [← hdual, torusCellDualOfPrimalEdge_of_mem L hePrimal]
    exact (torusCellCrossing L ⟨s(p, q), hePrimal⟩).2
  have hprimal : torusCellPrimalOfDualEdge L s(f, g) = s(p, q) := by
    rw [← hdual]
    exact torusCellPrimalOfDualOfPrimalEdge L hePrimal
  have hpS : p ∈ S := SimpleGraph.Reachable.refl p
  have hqS : q ∉ S := hmerge
  have hBadj : B.Adj f g := by
    refine ⟨?_, ?_⟩
    · simpa only [SimpleGraph.mem_edgeFinset] using heDual
    · rw [hprimal, torusCellEdgeStraddles_mk]
      exact iff_of_true hpS hqS
  have hEven : ∀ z, Even (B.degree z) :=
    torusCellCutDualGraph_degree_even L S
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even B hEven hBadj
  let c' := c.mapLe hle
  have hcyc' : c'.IsCycle := hcyc.mapLe hle
  have hedge' : s(f, g) ∈ c'.edges := by
    simpa [c', SimpleGraph.Walk.edges_mapLe_eq_edges] using hedge
  exact (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
    (G := torusCellDualCutGraph L G)).mpr
      ⟨u, c', hcyc', hedge'⟩ |>.2




theorem torusCellFaceCount_sup_edge_le
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) {p q : ZMod L × ZMod L}
    (hpq : (onsTorusGraph L).Adj p q) :
    torusCellFaceCount L (G ⊔ edge p q) ≤ torusCellFaceCount L G + 1 := by
  unfold torusCellFaceCount
  rw [torusCellDualCutGraph_sup_edge L G hpq]
  exact ecc_deleteEdge_card_le (torusCellDualCutGraph L G)
    (torusCellDualOfPrimalEdge L s(p, q))



theorem torusCellDefect_le_sup_edge_of_reachable
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) {p q : ZMod L × ZMod L}
    (hpq : (onsTorusGraph L).Adj p q) (hnew : ¬ G.Adj p q)
    (hreach : G.Reachable p q) :
    torusCellDefect L G ≤ torusCellDefect L (G ⊔ edge p q) := by
  have hedge := card_edgeSet_sup_edge G hpq.ne hnew
  have hcomp := card_components_sup_edge_of_reachable G p q hreach
  have hface := torusCellFaceCount_sup_edge_le L G hpq
  unfold torusCellDefect
  rw [hedge, hcomp]
  push_cast
  omega



theorem torusCellFaceCount_sup_edge_of_not_reachable
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) {p q : ZMod L × ZMod L}
    (hpq : (onsTorusGraph L).Adj p q)
    (hmerge : ¬ G.Reachable p q) :
    torusCellFaceCount L (G ⊔ edge p q) = torusCellFaceCount L G := by
  classical
  let D := torusCellDualCutGraph L G
  let ed := torusCellDualOfPrimalEdge L s(p, q)
  generalize hed : ed = e
  induction e using Sym2.inductionOn with
  | _ f g =>
      have hePrimal : s(p, q) ∈ (onsTorusGraph L).edgeFinset := by
        simpa only [SimpleGraph.mem_edgeFinset] using hpq
      have heDual : s(f, g) ∈ (onsTorusGraph L).edgeFinset := by
        rw [← hed]
        simp only [ed]
        rw [torusCellDualOfPrimalEdge_of_mem L hePrimal]
        exact (torusCellCrossing L ⟨s(p, q), hePrimal⟩).2
      have hprimal : torusCellPrimalOfDualEdge L s(f, g) = s(p, q) := by
        rw [← hed]
        simp only [ed]
        exact torusCellPrimalOfDualOfPrimalEdge L hePrimal
      have heD : D.Adj f g := by
        refine ⟨?_, ?_⟩
        · simpa only [SimpleGraph.mem_edgeFinset] using heDual
        · change torusCellPrimalOfDualEdge L s(f, g) ∉ G.edgeSet
          rw [hprimal, SimpleGraph.mem_edgeSet]
          exact fun hadj => hmerge hadj.reachable
      have hr : (D.deleteEdges {s(f, g)}).Reachable f g := by
        apply torusCellDualCutGraph_crossed_reachable_of_primal_not_reachable
          L G hpq hmerge
        simpa only [ed] using hed
      have hcard := ecc_deleteEdge_card_nonbridge D heD hr
      unfold torusCellFaceCount
      rw [torusCellDualCutGraph_sup_edge L G hpq]
      simpa only [D, ed, hed] using hcard


theorem torusCellDefect_sup_edge_of_not_reachable
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) {p q : ZMod L × ZMod L}
    (hpq : (onsTorusGraph L).Adj p q)
    (hmerge : ¬ G.Reachable p q) :
    torusCellDefect L (G ⊔ edge p q) = torusCellDefect L G := by
  have hnew : ¬ G.Adj p q := fun h => hmerge h.reachable
  have hedge := card_edgeSet_sup_edge G hpq.ne hnew
  have hcomp := card_components_sup_edge_of_not_reachable G p q hmerge
  have hface := torusCellFaceCount_sup_edge_of_not_reachable L G hpq hmerge
  unfold torusCellDefect
  rw [hedge, hface]
  push_cast
  omega



theorem torusCellDefect_le_sup_edge
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) {p q : ZMod L × ZMod L}
    (hpq : (onsTorusGraph L).Adj p q) (hnew : ¬ G.Adj p q) :
    torusCellDefect L G ≤ torusCellDefect L (G ⊔ edge p q) := by
  by_cases hreach : G.Reachable p q
  · exact torusCellDefect_le_sup_edge_of_reachable L G hpq hnew hreach
  · exact (torusCellDefect_sup_edge_of_not_reachable L G hpq hreach).ge





theorem torusCellDefect_nonnegative
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L))
    (hconn : (onsTorusGraph L).Connected)
    (hG : G ≤ onsTorusGraph L) :
    0 ≤ torusCellDefect L G := by
  classical
  generalize hn : G.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
      rcases Nat.eq_zero_or_pos n with hz | hpos
      · subst hz
        have hempty : G.edgeSet = ∅ :=
          (Set.ncard_eq_zero (Set.toFinite G.edgeSet)).mp hn
        have hbot : G = ⊥ := by
          rw [← SimpleGraph.edgeSet_eq_empty]
          exact hempty
        subst G
        rw [torusCellDefect_bot L hconn]
      · have hne : G.edgeSet.Nonempty := by
          rw [← Set.ncard_pos (Set.toFinite _), hn]
          exact hpos
        obtain ⟨e, he⟩ := hne
        obtain ⟨p, q⟩ := e
        let G' := G.deleteEdges {s(p, q)}
        have hGeq : G = G' ⊔ edge p q :=
          deleteEdges_sup_edge_eq G p q he
        have hdrop : G'.edgeSet.ncard + 1 = G.edgeSet.ncard :=
          card_edgeSet_deleteEdges_add_one G p q he
        have hn' : G'.edgeSet.ncard = n - 1 := by omega
        have hG' : G' ≤ onsTorusGraph L :=
          le_trans (SimpleGraph.deleteEdges_le _) hG
        have ihG' : 0 ≤ torusCellDefect L G' := by
          exact ih (n - 1) (by omega) G' hG' hn'
        have hpqG : G.Adj p q := by
          simpa only [SimpleGraph.mem_edgeSet] using he
        have hpq : (onsTorusGraph L).Adj p q := hG hpqG
        have hnew : ¬ G'.Adj p q := by
          rw [SimpleGraph.deleteEdges_adj]
          simp
        have hstep := torusCellDefect_le_sup_edge L G' hpq hnew
        rw [← hGeq] at hstep
        exact ihG'.trans hstep


theorem torusCellDefect_le_two
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L))
    (hconn : (onsTorusGraph L).Connected)
    (hG : G ≤ onsTorusGraph L) :
    torusCellDefect L G ≤ 2 := by
  have hdual := torusCellDefect_nonnegative L
    (torusCellDualCutGraph L G) hconn (fun _ _ h => h.1)
  have hsum := torusCellDefect_add_dualCutGraph L G hG
  omega



theorem torusCellDefect_classified
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L))
    (hconn : (onsTorusGraph L).Connected)
    (hG : G ≤ onsTorusGraph L) :
    torusCellDefect L G = 0 ∨ torusCellDefect L G = 1 ∨
      torusCellDefect L G = 2 := by
  have h0 := torusCellDefect_nonnegative L G hconn hG
  have h2 := torusCellDefect_le_two L G hconn hG
  omega


theorem torusCellDefect_nonnegative_unconditional
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L))
    (hG : G ≤ onsTorusGraph L) :
    0 ≤ torusCellDefect L G :=
  torusCellDefect_nonnegative L G (onsTorusGraph_connected L) hG


theorem torusCellDefect_le_two_unconditional
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L))
    (hG : G ≤ onsTorusGraph L) :
    torusCellDefect L G ≤ 2 :=
  torusCellDefect_le_two L G (onsTorusGraph_connected L) hG


theorem torusCellDefect_classified_unconditional
    (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L))
    (hG : G ≤ onsTorusGraph L) :
    torusCellDefect L G = 0 ∨ torusCellDefect L G = 1 ∨
      torusCellDefect L G = 2 :=
  torusCellDefect_classified L G (onsTorusGraph_connected L) hG

end StatMech.BeffaraDC
