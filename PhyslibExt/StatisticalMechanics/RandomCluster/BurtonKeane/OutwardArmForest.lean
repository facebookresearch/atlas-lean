/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OutwardArm

/-!
# A tree where forest peeling fails

When the root's arms cover all its children, no outward arm exists; a ten-vertex tree is an explicit
example.

## i. Overview

`oaf_cutGraph G x` deletes the vertex `x`. Abstract forest peeling (`oaf_AbstractForestPeel`) asks
each vertex of `T` for a reachable vertex outside `T` that no other vertex of `T` reaches once it is
deleted. If every arm of the root contains another vertex of `T`, this fails. The tree `OafTree.G`
(a root with three children, each with two leaves) and `T` = root and children is such an example.
The file also records that a finite tree has fewer branch vertices than leaves.

## ii. Key results

- `oaf_outwardArm_false_of_rootCover` : covered root arms exclude outward arms
- `oaf_tree_not_forestPeel` : the ten-vertex tree is a counterexample to forest peeling
- `oaf_tree_internal_lt_leaves` : branch vertices are fewer than leaves in a finite tree

## iii. Table of contents

- A. Definitions
- B. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset
open scoped BigOperators

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Definitions -/

/-- The graph `G` with the vertex `x` deleted. -/
def oaf_cutGraph {V : Type*} (G : SimpleGraph V) (x : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ≠ x ∧ b ≠ x
  symm := ⟨by rintro a b ⟨h, ha, hb⟩; exact ⟨h.symm, hb, ha⟩⟩
  loopless := ⟨fun a h => G.irrefl h.1⟩

/-! ## B. Results -/

lemma oaf_openSubgraph_removeSite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
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

lemma oaf_connected_removeSite_iff (ω : ConfigSpace (Sym2 (Site d))) (x a b : Site d) :
    Lattice.Connected d (removeSite x ω) a b ↔
      (oaf_cutGraph (openSubgraph d ω) x).Reachable a b := by
  unfold Lattice.Connected
  rw [oaf_openSubgraph_removeSite]

lemma oaf_outwardArm_false_of_rootCover (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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

/-- Abstract forest peeling for `T` in `G`: each vertex of `T` reaches a vertex outside `T` that no
other vertex of `T` reaches once it is deleted. -/
def oaf_AbstractForestPeel {V : Type*} [DecidableEq V] (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ x ∈ T, ∃ a, G.Reachable x a ∧ a ∉ T ∧
    (∀ y ∈ T, y ≠ x → ¬ (oaf_cutGraph G x).Reachable a y)

lemma oaf_abstractForestPeel_false_of_rootCover {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) {r : V} {c : Fin 3 → V}
    (hrT : r ∈ T) (hcT : ∀ i, c i ∈ T) (hcne : ∀ i, c i ≠ r)
    (hcover : ∀ a, G.Reachable r a → a ∉ T → ∃ i, (oaf_cutGraph G r).Reachable a (c i)) :
    ¬ oaf_AbstractForestPeel G T := by
  intro h
  obtain ⟨a, hra, haT, hpriv⟩ := h r hrT
  obtain ⟨i, hai⟩ := hcover a hra haT
  exact hpriv (c i) (hcT i) (hcne i) hai

lemma oaf_reach_eqLabel {V L : Type*} (H : SimpleGraph V) (φ : V → L)
    (hφ : ∀ a b, H.Adj a b → φ a = φ b) {x y : V} (h : H.Reachable x y) : φ x = φ y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (hφ _ _ hadj).trans ih

namespace OafTree

/-- The vertex type of the ten-vertex tree. -/
abbrev V := Fin 10

/-- The child subtree containing each vertex (the root is assigned to `0`). -/
def sub : V → Fin 3 := fun v =>
  match v with
  | 1 => 0 | 4 => 0 | 5 => 0
  | 2 => 1 | 6 => 1 | 7 => 1
  | 3 => 2 | 8 => 2 | 9 => 2
  | _ => 0

/-- Edges of the ten-vertex tree: a root, three children, two leaves per child. -/
def edges : List (V × V) := [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(2,7),(3,8),(3,9)]

/-- Adjacency relation of the ten-vertex tree. -/
def E (a b : V) : Prop := (a, b) ∈ edges ∨ (b, a) ∈ edges

/-- The ten-vertex tree relation is decidable. -/
instance : DecidableRel E := by unfold E; intro a b; infer_instance

/-- The ten-vertex tree. -/
def G : SimpleGraph V := SimpleGraph.fromRel E

/-- Adjacency in the ten-vertex tree is decidable. -/
instance instGAdj : DecidableRel G.Adj := by unfold G fromRel; intro a b; infer_instance

/-- Adjacency in the tree with the root deleted is decidable. -/
instance instCutAdj : DecidableRel (oaf_cutGraph G 0).Adj := fun a b => by
  unfold oaf_cutGraph; infer_instance

/-- The three children of the root. -/
def child : Fin 3 → V := ![1, 2, 3]

/-- The root and its three children. -/
def Ttree : Finset V := {0, 1, 2, 3}

lemma oaf_sub_const_on_cut : ∀ a b, (oaf_cutGraph G 0).Adj a b → sub a = sub b := by decide

lemma oaf_children_separated (i j : Fin 3) (hij : i ≠ j) :
    ¬ (oaf_cutGraph G 0).Reachable (child i) (child j) := by
  intro h
  have hlab := oaf_reach_eqLabel (oaf_cutGraph G 0) sub oaf_sub_const_on_cut h
  fin_cases i <;> fin_cases j <;> simp_all [child, sub]

lemma oaf_adj_reach {a b : V} (h : G.Adj a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    (oaf_cutGraph G 0).Reachable a b :=
  SimpleGraph.Adj.reachable (G := oaf_cutGraph G 0) ⟨h, ha, hb⟩

lemma oaf_cover_leaf (a : V) (haT : a ∉ Ttree) :
    (oaf_cutGraph G 0).Reachable a (child (sub a)) := by
  fin_cases a <;>
    first
      | exact absurd (by decide : (_ : V) ∈ Ttree) haT
      | exact oaf_adj_reach (by unfold G fromRel E edges; decide) (by decide) (by decide)

lemma oaf_edge_reach {a b : V} (h : G.Adj a b) : G.Reachable a b :=
  SimpleGraph.Adj.reachable h

private lemma oaf_adj01 : G.Adj 0 1 := by unfold G fromRel E edges; decide
private lemma oaf_adj02 : G.Adj 0 2 := by unfold G fromRel E edges; decide
private lemma oaf_adj03 : G.Adj 0 3 := by unfold G fromRel E edges; decide

lemma oaf_root_reach (a : V) : G.Reachable 0 a := by
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

lemma oaf_tree_not_forestPeel : ¬ oaf_AbstractForestPeel G Ttree := by
  refine oaf_abstractForestPeel_false_of_rootCover G Ttree (r := 0) (c := child) ?_ ?_ ?_ ?_
  · decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro a _ haT
    exact ⟨sub a, oaf_cover_leaf a haT⟩

lemma oaf_root_deg : 3 ≤ G.degree 0 := by decide

lemma oaf_child_deg : ∀ i : Fin 3, 3 ≤ G.degree (child i) := by decide

end OafTree

lemma oaf_deg_pos_of_connected {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
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

lemma oaf_tree_internal_lt_leaves {V : Type*} [Fintype V] (G : SimpleGraph V)
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
      simp only [ite_eq_left h3, ite_eq_right hne1]; linarith
    · by_cases h1' : G.degree v = 1
      · have h1cast : (G.degree v : ℤ) = 1 := by exact_mod_cast h1'
        simp only [ite_eq_right h3, ite_eq_left h1']; linarith
      · have h2 : G.degree v = 2 := by omega
        have h2cast : (G.degree v : ℤ) = 2 := by exact_mod_cast h2
        simp only [ite_eq_right h3, ite_eq_right h1']; linarith
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
