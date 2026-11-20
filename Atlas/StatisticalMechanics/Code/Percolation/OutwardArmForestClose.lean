/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.SpanningTreeArmClose
import Code.Percolation.BKForestLib
import Code.Percolation.ForestLeafDisjointClose

open Set SimpleGraph Finset
open scoped BigOperators

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}










def oaf_cutGraph {V : Type*} (G : SimpleGraph V) (x : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ≠ x ∧ b ≠ x
  symm := by rintro a b ⟨h, ha, hb⟩; exact ⟨h.symm, hb, ha⟩
  loopless := ⟨fun a h => G.irrefl h.1⟩





theorem oaf_openSubgraph_removeSite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    openSubgraph d (removeSite x ω) = oaf_cutGraph (openSubgraph d ω) x := by
  ext a b
  simp only [openSubgraph_adj, oaf_cutGraph]
  constructor
  · rintro ⟨hadj, hopen⟩
    have hxnotin : x ∉ s(a, b) := by
      intro hx
      rw [removeSite_apply_of_mem hx] at hopen
      exact Bool.false_ne_true hopen
    rw [removeSite_apply_of_notMem hxnotin] at hopen
    refine ⟨⟨hadj, hopen⟩, ?_, ?_⟩
    · rintro rfl; exact hxnotin (Sym2.mem_mk_left a b)
    · rintro rfl; exact hxnotin (Sym2.mem_mk_right a b)
  · rintro ⟨⟨hadj, hopen⟩, hax, hbx⟩
    have hxnotin : x ∉ s(a, b) := by
      rw [Sym2.mem_iff]
      rintro (h | h)
      · exact hax h.symm
      · exact hbx h.symm
    exact ⟨hadj, by rw [removeSite_apply_of_notMem hxnotin]; exact hopen⟩



theorem oaf_connected_removeSite_iff (ω : ConfigSpace (Sym2 (Site d))) (x a b : Site d) :
    Lattice.Connected d (removeSite x ω) a b ↔
      (oaf_cutGraph (openSubgraph d ω) x).Reachable a b := by
  unfold Lattice.Connected
  rw [oaf_openSubgraph_removeSite]






















theorem oaf_outwardArm_false_of_rootCover (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {r : Site d} {c : Fin 3 → Site d}
    (hrbox : r ∈ box d n) (htri_r : IsTrifurcation d ω r)
    (hcT : ∀ i, c i ∈ tfc_trifFinset ω n)
    (hcne : ∀ i, c i ≠ r)
    (hcover : ∀ a, Connected d ω r a → a ≠ r →
        ∃ i, Connected d (removeSite r ω) a (c i)) :
    ¬ fld_OutwardArm ω n := by
  intro h
  obtain ⟨a, ⟨_habox, hra, hainf⟩, hpriv, _hfar⟩ := h r hrbox htri_r
  
  have haT : a ∉ tfc_trifFinset ω n := stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω hainf
  
  have hane : a ≠ r := by
    intro he; exact haT (he ▸ tfc_mem_trifFinset.mpr ⟨hrbox, htri_r⟩)
  
  obtain ⟨i, hai⟩ := hcover a hra hane
  exact hpriv (c i) (hcT i) (hcne i) hai











def oaf_AbstractForestPeel {V : Type*} [DecidableEq V] (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ x ∈ T, ∃ a, G.Reachable x a ∧ a ∉ T ∧
    (∀ y ∈ T, y ≠ x → ¬ (oaf_cutGraph G x).Reachable a y)





theorem oaf_abstractForestPeel_false_of_rootCover {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) {r : V} {c : Fin 3 → V}
    (hrT : r ∈ T) (hcT : ∀ i, c i ∈ T) (hcne : ∀ i, c i ≠ r)
    (hcover : ∀ a, G.Reachable r a → a ∉ T → ∃ i, (oaf_cutGraph G r).Reachable a (c i)) :
    ¬ oaf_AbstractForestPeel G T := by
  intro h
  obtain ⟨a, hra, haT, hpriv⟩ := h r hrT
  obtain ⟨i, hai⟩ := hcover a hra haT
  exact hpriv (c i) (hcT i) (hcne i) hai









theorem oaf_reach_eqLabel {V L : Type*} (H : SimpleGraph V) (φ : V → L)
    (hφ : ∀ a b, H.Adj a b → φ a = φ b) {x y : V} (h : H.Reachable x y) : φ x = φ y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (hφ _ _ hadj).trans ih










namespace OafTree


abbrev V := Fin 10


def sub : V → Fin 3 := fun v =>
  match v with
  | 1 => 0 | 4 => 0 | 5 => 0
  | 2 => 1 | 6 => 1 | 7 => 1
  | 3 => 2 | 8 => 2 | 9 => 2
  | _ => 0


def edges : List (V × V) := [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(2,7),(3,8),(3,9)]


def E (a b : V) : Prop := (a, b) ∈ edges ∨ (b, a) ∈ edges

instance : DecidableRel E := by unfold E; intro a b; infer_instance


def G : SimpleGraph V := SimpleGraph.fromRel E

instance instGAdj : DecidableRel G.Adj := by unfold G fromRel; intro a b; infer_instance

instance instCutAdj : DecidableRel (oaf_cutGraph G 0).Adj := fun a b => by
  unfold oaf_cutGraph; infer_instance


def child : Fin 3 → V := ![1, 2, 3]


def Ttree : Finset V := {0, 1, 2, 3}



theorem oaf_sub_const_on_cut : ∀ a b, (oaf_cutGraph G 0).Adj a b → sub a = sub b := by decide





theorem oaf_children_separated (i j : Fin 3) (hij : i ≠ j) :
    ¬ (oaf_cutGraph G 0).Reachable (child i) (child j) := by
  intro h
  have hlab := oaf_reach_eqLabel (oaf_cutGraph G 0) sub oaf_sub_const_on_cut h
  fin_cases i <;> fin_cases j <;> simp_all [child, sub]


theorem oaf_adj_reach {a b : V} (h : G.Adj a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    (oaf_cutGraph G 0).Reachable a b :=
  SimpleGraph.Adj.reachable (G := oaf_cutGraph G 0) ⟨h, ha, hb⟩



theorem oaf_cover_leaf (a : V) (haT : a ∉ Ttree) :
    (oaf_cutGraph G 0).Reachable a (child (sub a)) := by
  fin_cases a <;>
    first
      
      | exact absurd (by decide : (_ : V) ∈ Ttree) haT
      
      | exact oaf_adj_reach (by unfold G fromRel E edges; decide) (by decide) (by decide)


theorem oaf_edge_reach {a b : V} (h : G.Adj a b) : G.Reachable a b :=
  SimpleGraph.Adj.reachable h

private theorem oaf_adj01 : G.Adj 0 1 := by unfold G fromRel E edges; decide
private theorem oaf_adj02 : G.Adj 0 2 := by unfold G fromRel E edges; decide
private theorem oaf_adj03 : G.Adj 0 3 := by unfold G fromRel E edges; decide


theorem oaf_root_reach (a : V) : G.Reachable 0 a := by
  fin_cases a
  · exact Reachable.refl _
  · exact oaf_edge_reach oaf_adj01
  · exact oaf_edge_reach oaf_adj02
  · exact oaf_edge_reach oaf_adj03
  · exact (oaf_edge_reach oaf_adj01).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))
  · exact (oaf_edge_reach oaf_adj01).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))
  · exact (oaf_edge_reach oaf_adj02).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))
  · exact (oaf_edge_reach oaf_adj02).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))
  · exact (oaf_edge_reach oaf_adj03).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))
  · exact (oaf_edge_reach oaf_adj03).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))





theorem oaf_tree_not_forestPeel : ¬ oaf_AbstractForestPeel G Ttree := by
  refine oaf_abstractForestPeel_false_of_rootCover G Ttree (r := 0) (c := child) ?_ ?_ ?_ ?_
  · decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro a _ haT
    exact ⟨sub a, oaf_cover_leaf a haT⟩


theorem oaf_root_deg : 3 ≤ G.degree 0 := by decide


theorem oaf_child_deg : ∀ i : Fin 3, 3 ≤ G.degree (child i) := by decide

end OafTree










theorem oaf_deg_pos_of_connected {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hV : 2 ≤ Fintype.card V) (v : V) : 1 ≤ G.degree v := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hV v
  have hr : G.Reachable v w := hconn.preconnected v w
  have hex : ∃ u, G.Adj v u := by
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact absurd rfl (Ne.symm hw)
    | cons hadj _ => exact ⟨_, hadj⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, G.degree_pos_iff_exists_adj]
  exact hex












theorem oaf_tree_internal_lt_leaves {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : G.IsTree) (hV : 2 ≤ Fintype.card V) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      < (univ.filter (fun v => G.degree v = 1)).card := by
  classical
  have hpos := oaf_deg_pos_of_connected G hT.connected hV
  have hhand : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hedge : G.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  set indI : V → ℤ := fun v => if 3 ≤ G.degree v then 1 else 0 with hindI
  set indL : V → ℤ := fun v => if G.degree v = 1 then 1 else 0 with hindL
  
  have hbound : ∀ v, (2 : ℤ) + indI v - indL v ≤ (G.degree v : ℤ) := by
    intro v
    simp only [hindI, hindL]
    have h1 := hpos v
    have hcast : (1 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h1
    by_cases h3 : 3 ≤ G.degree v
    · have hne1 : ¬ G.degree v = 1 := by omega
      have h3cast : (3 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h3
      simp only [if_pos h3, if_neg hne1]; linarith
    · by_cases h1' : G.degree v = 1
      · have h1cast : (G.degree v : ℤ) = 1 := by exact_mod_cast h1'
        simp only [if_neg h3, if_pos h1']; linarith
      · have h2 : G.degree v = 2 := by omega
        have h2cast : (G.degree v : ℤ) = 2 := by exact_mod_cast h2
        simp only [if_neg h3, if_neg h1']; linarith
  have hsumbound : ∑ v, ((2 : ℤ) + indI v - indL v) ≤ ∑ v, (G.degree v : ℤ) :=
    Finset.sum_le_sum (fun v _ => hbound v)
  
  have hLHS : ∑ v, ((2 : ℤ) + indI v - indL v)
      = 2 * Fintype.card V + (univ.filter (fun v => 3 ≤ G.degree v)).card
        - (univ.filter (fun v => G.degree v = 1)).card := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [hindI, hindL, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_boole, Finset.sum_boole]
    ring
  
  have hRHS : ∑ v, (G.degree v : ℤ) = 2 * Fintype.card V - 2 := by
    have h : (∑ v, (G.degree v : ℤ)) = ((∑ v, G.degree v : ℕ) : ℤ) := by
      rw [Nat.cast_sum]
    rw [h, hhand]; omega
  rw [hLHS, hRHS] at hsumbound
  
  have hfin : ((univ.filter (fun v => 3 ≤ G.degree v)).card : ℤ)
      < ((univ.filter (fun v => G.degree v = 1)).card : ℤ) := by linarith
  exact_mod_cast hfin

end Percolation

end StatMech
