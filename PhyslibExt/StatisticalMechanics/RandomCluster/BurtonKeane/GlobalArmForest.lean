/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Order.Filter.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanForestArms
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestReaching
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmReachComponent
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutAcyclic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutSpanning
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmInjectionCount

/-!
# Global arm forests

A forest of open arms from each trifurcation to the boundary, with three arms per trifurcation,
bounds the trifurcation count by the boundary size.

## i. Overview

`bc51_GlobalArmForest ω n` is an acyclic subgraph of the open subgraph whose arms join every
trifurcation of `B_n` to three boundary sites. Vertex-disjoint arms give the arm-forest reaching
property and the bound `Tcount ≤ |∂B_n|`. The file also gives the small examples `catG` (a tree with
two branch vertices) and `cycleG` (the same with an extra edge, not acyclic) used to test the forest
conditions.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `bc51_armForestReaching_of_globalArmForest` : a global arm forest gives arm-forest reaching
- `bc51_Tcount_le_boundary_of_globalArmForest` : the counting bound
- `bc51_globalArmForest_of_forestCover` : a forest cover gives a global arm forest
- `catG_internal_lt_leaves` : in the example tree, branch vertices are fewer than leaves

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma bc51_arms_edgeDisjoint (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x c0 c1 z0 z1 : Site d}
    (w0 : T.Walk c0 z0) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1x : x ∉ w1.support)
    (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
    ∀ e, e ∈ w0.edges → e ∈ w1.edges → False := by
  intro e he0 he1
  have hd := Percolation.sfa_armWalks_disjoint ω T hπ w0 hw0x w1 hw1x hcut
  induction e using Sym2.ind with
  | _ u v =>
    exact hd u (w0.fst_mem_support_of_mem_edges he0) (w1.fst_mem_support_of_mem_edges he1)

open Classical in
/-- A global arm forest for `B_n`: an acyclic open subgraph on finitely many sites, with three arms
from every trifurcation to boundary sites, the arms of distinct trifurcations disjoint. -/
def bc51_GlobalArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (c : Site d → Fin 3 → Site d) (zr : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d n) ∧
    ((∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) ∨ (∃ v, spc_OnBPath T B v)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      (∀ i, T.Adj x (c x i)) ∧
      (¬ Connected d (removeSite x ω) (c x 0) (c x 1) ∧
       ¬ Connected d (removeSite x ω) (c x 0) (c x 2) ∧
       ¬ Connected d (removeSite x ω) (c x 1) (c x 2)) ∧
      (∀ i, zr x i ∈ B ∧ ∃ w : T.Walk (c x i) (zr x i), x ∉ w.support))

lemma bc51_survivor_of_trif (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) (B : Set (Site d))
    {x : Site d} {c zr : Fin 3 → Site d}
    (hadj : ∀ i, T.Adj x (c i))
    (hcut01 : ¬ Connected d (removeSite x ω) (c 0) (c 1))
    (hreach : ∀ i, zr i ∈ B ∧ ∃ w : T.Walk (c i) (zr i), x ∉ w.support) :
    spc_OnBPath T B x := by
  obtain ⟨hz0, w0, hw0x⟩ := hreach 0
  obtain ⟨hz1, w1, hw1x⟩ := hreach 1
  exact (sfa_onBPath_of_arms ω T hπ B (hadj 0) (hadj 1) w0 hw0x hz0 w1 hw1x hz1 hcut01).1

lemma bc51_armForestReaching_of_globalArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc51_GlobalArmForest ω n) : sfa_ArmForestReaching ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hsurv, hData⟩ := h
  have hRne : ∃ v, spc_OnBPath T B v := by
    rcases hsurv with ⟨x, hxbox, htri⟩ | hbase
    · obtain ⟨hadj, ⟨hcut01, _, _⟩, hreach⟩ := hData x hxbox htri
      exact ⟨x, bc51_survivor_of_trif ω T hTopen B hadj hcut01 hreach⟩
    · exact hbase
  exact ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩

lemma bc51_Tcount_le_boundary_of_globalArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc51_GlobalArmForest ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  sfa_Tcount_le_boundary_of_armForestReaching ω n
    (bc51_armForestReaching_of_globalArmForest ω n h)

lemma bc51_cutWalk_lift {x a b : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (w : (openSubgraph d (removeSite x ω)).Walk a b) (hwx : x ∉ w.support) :
    ∃ w' : (openSubgraph d ω).Walk a b, x ∉ w'.support ∧
      (∀ e, e ∈ w'.edges → e ∈ (openSubgraph d ω).edgeSet) := by
  classical
  refine ⟨w.mapLe (bc42_removeSite_openSubgraph_le x ω), ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hwx
  · intro e he; exact (w.mapLe (bc42_removeSite_openSubgraph_le x ω)).edges_subset_edgeSet he

lemma bc51_walk_transfer_to_T {a b x : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (T : SimpleGraph (Site d)) (w' : (openSubgraph d ω).Walk a b) (hwx : x ∉ w'.support)
    (hcov : ∀ e, e ∈ w'.edges → e ∈ T.edgeSet) :
    ∃ w : T.Walk a b, x ∉ w.support := by
  refine ⟨w'.transfer T hcov, ?_⟩
  rw [SimpleGraph.Walk.support_transfer]; exact hwx

open Classical in
lemma bc51_globalArmForest_of_forestCover (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (hTdec : DecidableRel T.Adj)
    (B : Set (Site d)) (c : Site d → Fin 3 → Site d) (zr : Site d → Fin 3 → Site d)
    (hTac : T.IsAcyclic)
    (hTopen : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    (hTsupp : ∀ u v, T.Adj u v → u ∈ Vall)
    (hBbd : B ⊆ vertexBoundary d n)
    (hsurv : (∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) ∨ (∃ v, spc_OnBPath T B v))
    (hData : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      (∀ i, T.Adj x (c x i)) ∧
      (¬ Connected d (removeSite x ω) (c x 0) (c x 1) ∧
       ¬ Connected d (removeSite x ω) (c x 0) (c x 2) ∧
       ¬ Connected d (removeSite x ω) (c x 1) (c x 2)) ∧
      (∀ i, zr x i ∈ B ∧ ∃ w : (openSubgraph d (removeSite x ω)).Walk (c x i) (zr x i),
        x ∉ w.support ∧
        (∀ e, e ∈ (w.mapLe (bc42_removeSite_openSubgraph_le x ω)).edges → e ∈ T.edgeSet))) :
    bc51_GlobalArmForest ω n := by
  classical
  refine ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hsurv, ?_⟩
  intro x hxbox htri
  obtain ⟨hadj, hcut, hreach⟩ := hData x hxbox htri
  refine ⟨hadj, hcut, ?_⟩
  intro i
  obtain ⟨hzr, w, hwx, hcov⟩ := hreach i
  refine ⟨hzr, ?_⟩
  obtain ⟨w', hw'x, _⟩ := bc51_cutWalk_lift w hwx
  exact bc51_walk_transfer_to_T T (w.mapLe (bc42_removeSite_openSubgraph_le x ω))
    (by rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hwx) hcov

open Classical in
lemma bc51_globalArmForest_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    bc51_GlobalArmForest ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, _hRne, hData⟩ :=
    sfa_armForestReaching_star ω n a hsingle hadj habdry hxne hainj hsep
  exact ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd,
    Or.inl ⟨x, hxbox, htri⟩, hData⟩

open Classical in
lemma bc51_globalArmForest_of_boundary_edge (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {b₁ b₂ : Site d} (hb1 : b₁ ∈ vertexBoundary d n) (hb2 : b₂ ∈ vertexBoundary d n)
    (hbne : b₁ ≠ b₂) (hopen : (openSubgraph d ω).Adj b₁ b₂)
    (hnotrif : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc51_GlobalArmForest ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ :=
    sfa_armForestReaching_of_boundary_edge ω n hb1 hb2 hbne hopen hnotrif
  exact ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, Or.inr hRne, hData⟩

namespace Bc51Witness

/-- Edges of a six-vertex tree with two branch vertices `0` and `1`. -/
def catE (a b : Fin 6) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
  (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨
  (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
  (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) ∨
  (a = 1 ∧ b = 5) ∨ (a = 5 ∧ b = 1)

/-- The example tree relation is decidable. -/
instance : DecidableRel catE := fun a b => by unfold catE; infer_instance

/-- The six-vertex example tree with two branch vertices. -/
def catG : SimpleGraph (Fin 6) := SimpleGraph.fromRel catE
/-- Adjacency in the example tree is decidable. -/
instance : DecidableRel catG.Adj := by unfold catG fromRel; intro a b; infer_instance

lemma catG_isTree : catG.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide

lemma catG_leafCount :
    (univ.filter (fun v => 3 ≤ catG.degree v)).card = 2 ∧
    (univ.filter (fun v => catG.degree v = 1)).card = 4 := by
  constructor <;> decide

lemma catG_internal_lt_leaves :
    (univ.filter (fun v => 3 ≤ catG.degree v)).card
      < (univ.filter (fun v => catG.degree v = 1)).card :=
  flc2_tree_internal_lt_leaves catG catG_isTree (by decide)

/-- The example tree relation with the extra edge `2 4`, which closes a cycle. -/
def cycleE (a b : Fin 6) : Prop := catE a b ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2)
/-- The example cycle relation is decidable. -/
instance : DecidableRel cycleE := fun a b => by unfold cycleE; infer_instance

/-- The example graph with a cycle. -/
def cycleG : SimpleGraph (Fin 6) := SimpleGraph.fromRel cycleE
/-- Adjacency in the example cycle graph is decidable. -/
instance : DecidableRel cycleG.Adj := by unfold cycleG fromRel; intro a b; infer_instance

lemma cycleG_not_acyclic : ¬ cycleG.IsAcyclic := by
  intro hac
  have h02 : cycleG.Adj 0 2 := by
    rw [cycleG, fromRel_adj]; refine ⟨by decide, ?_⟩; left; unfold cycleE catE; decide
  have h24 : cycleG.Adj 2 4 := by
    rw [cycleG, fromRel_adj]; refine ⟨by decide, ?_⟩; left; unfold cycleE; decide
  have h41 : cycleG.Adj 4 1 := by
    rw [cycleG, fromRel_adj]; refine ⟨by decide, ?_⟩; left; unfold cycleE catE; decide
  have h10 : cycleG.Adj 1 0 := by
    rw [cycleG, fromRel_adj]; refine ⟨by decide, ?_⟩; left; unfold cycleE catE; decide
  refine hac (Walk.cons h02 (Walk.cons h24 (Walk.cons h41 (Walk.cons h10 Walk.nil)))) ?_
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, by simp, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]
    decide
  · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
    decide

lemma catG_subgraph_acyclic {H : SimpleGraph (Fin 6)} (hsub : H ≤ catG) : H.IsAcyclic :=
  SimpleGraph.IsAcyclic.anti hsub catG_isTree.isAcyclic

end Bc51Witness

lemma bc51_forestCover_nonvacuous_nilWalk {x a : Site d}
    {ω : ConfigSpace (Sym2 (Site d))} (T : SimpleGraph (Site d))
    (hax : a ≠ x) :
    let w : (openSubgraph d (removeSite x ω)).Walk a a := Walk.nil
    x ∉ w.support ∧
      (∀ e, e ∈ (w.mapLe (bc42_removeSite_openSubgraph_le x ω)).edges → e ∈ T.edgeSet) := by
  refine ⟨?_, ?_⟩
  · simpa using (Ne.symm hax)
  · intro e he
    simp only [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.map_nil] at he
    exact absurd he (List.not_mem_nil)

end StatMech.Walls
