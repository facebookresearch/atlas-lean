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
import Code.Percolation.SecondPeelingClose
import Code.Percolation.SpanForestArmsClose
import Code.Percolation.ArmReachComponentClose
import Code.Percolation.ForestLeafCountClose
import Code.Walls.bc38acyclic
import Code.Walls.bc39spanning
import Code.Walls.bc50arminjection

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}












theorem bc51_subgraph_isAcyclic {V : Type*} {T T' : SimpleGraph V} (hsub : T ≤ T')
    (h : T'.IsAcyclic) : T.IsAcyclic :=
  h.anti hsub













theorem bc51_arms_vertexDisjoint (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x c0 c1 z0 z1 : Site d}
    (w0 : T.Walk c0 z0) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1x : x ∉ w1.support)
    (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
    ∀ v, v ∈ w0.support → v ∈ w1.support → False :=
  sfa_armWalks_disjoint ω T hπ w0 hw0x w1 hw1x hcut



theorem bc51_arms_edgeDisjoint (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x c0 c1 z0 z1 : Site d}
    (w0 : T.Walk c0 z0) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1x : x ∉ w1.support)
    (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
    ∀ e, e ∈ w0.edges → e ∈ w1.edges → False := by
  intro e he0 he1
  
  have hd := bc51_arms_vertexDisjoint ω T hπ w0 hw0x w1 hw1x hcut
  induction e using Sym2.ind with
  | _ u v =>
    exact hd u (w0.fst_mem_support_of_mem_edges he0) (w1.fst_mem_support_of_mem_edges he1)















open Classical in














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






theorem bc51_survivor_of_trif (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) (B : Set (Site d))
    {x : Site d} {c zr : Fin 3 → Site d}
    (hadj : ∀ i, T.Adj x (c i))
    (hcut01 : ¬ Connected d (removeSite x ω) (c 0) (c 1))
    (hreach : ∀ i, zr i ∈ B ∧ ∃ w : T.Walk (c i) (zr i), x ∉ w.support) :
    spc_OnBPath T B x := by
  obtain ⟨hz0, w0, hw0x⟩ := hreach 0
  obtain ⟨hz1, w1, hw1x⟩ := hreach 1
  exact (sfa_onBPath_of_arms ω T hπ B (hadj 0) (hadj 1) w0 hw0x hz0 w1 hw1x hz1 hcut01).1









theorem bc51_armForestReaching_of_globalArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc51_GlobalArmForest ω n) : sfa_ArmForestReaching ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hsurv, hData⟩ := h
  
  have hRne : ∃ v, spc_OnBPath T B v := by
    rcases hsurv with ⟨x, hxbox, htri⟩ | hbase
    · 
      obtain ⟨hadj, ⟨hcut01, _, _⟩, hreach⟩ := hData x hxbox htri
      exact ⟨x, bc51_survivor_of_trif ω T hTopen B hadj hcut01 hreach⟩
    · exact hbase
  exact ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩




theorem bc51_Tcount_le_boundary_of_globalArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc51_GlobalArmForest ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  sfa_Tcount_le_boundary_of_armForestReaching ω n
    (bc51_armForestReaching_of_globalArmForest ω n h)




















open Classical in










def bc51_ArmForestEmbedding (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
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







theorem bc51_armForestEmbedding_iff_globalArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc51_ArmForestEmbedding ω n ↔ bc51_GlobalArmForest ω n :=
  Iff.rfl






theorem bc51_armForestReaching_of_armEmbedding (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc51_ArmForestEmbedding ω n) : sfa_ArmForestReaching ω n :=
  bc51_armForestReaching_of_globalArmForest ω n
    ((bc51_armForestEmbedding_iff_globalArmForest ω n).mp h)











theorem bc51_openSubgraph_removeSite_le (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (removeSite x ω) ≤ openSubgraph d ω := by
  intro u v h
  obtain ⟨hlat, hopen⟩ := h
  refine ⟨hlat, ?_⟩
  by_cases hx : x ∈ (s(u, v) : Sym2 (Site d))
  · rw [removeSite_apply_of_mem hx] at hopen; exact absurd hopen (by simp)
  · rwa [removeSite_apply_of_notMem hx] at hopen




theorem bc51_cutWalk_lift {x a b : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (w : (openSubgraph d (removeSite x ω)).Walk a b) (hwx : x ∉ w.support) :
    ∃ w' : (openSubgraph d ω).Walk a b, x ∉ w'.support ∧
      (∀ e, e ∈ w'.edges → e ∈ (openSubgraph d ω).edgeSet) := by
  classical
  refine ⟨w.mapLe (bc51_openSubgraph_removeSite_le x ω), ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hwx
  · intro e he; exact (w.mapLe (bc51_openSubgraph_removeSite_le x ω)).edges_subset_edgeSet he











theorem bc51_walk_transfer_to_T {a b x : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (T : SimpleGraph (Site d)) (w' : (openSubgraph d ω).Walk a b) (hwx : x ∉ w'.support)
    (hcov : ∀ e, e ∈ w'.edges → e ∈ T.edgeSet) :
    ∃ w : T.Walk a b, x ∉ w.support := by
  refine ⟨w'.transfer T hcov, ?_⟩
  rw [SimpleGraph.Walk.support_transfer]; exact hwx


















open Classical in












theorem bc51_globalArmForest_of_forestCover (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
        (∀ e, e ∈ (w.mapLe (bc51_openSubgraph_removeSite_le x ω)).edges → e ∈ T.edgeSet))) :
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
  
  exact bc51_walk_transfer_to_T T (w.mapLe (bc51_openSubgraph_removeSite_le x ω))
    (by rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hwx) hcov






















theorem bc51_arc_perArm_reaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hres : arc_TrifArmsRemoveSiteInfinite ω n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
      (∀ i, (openSubgraph d ω).Adj x (c i)) ∧
      (∀ i, c i ≠ x) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
      (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧
        ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) :=
  arc_trif_arm_data ω n hres x hxbox htri

open Classical in





theorem bc51_globalArmForest_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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




theorem bc51_globalArmForest_of_boundary_edge (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {b₁ b₂ : Site d} (hb1 : b₁ ∈ vertexBoundary d n) (hb2 : b₂ ∈ vertexBoundary d n)
    (hbne : b₁ ≠ b₂) (hopen : (openSubgraph d ω).Adj b₁ b₂)
    (hnotrif : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc51_GlobalArmForest ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ :=
    sfa_armForestReaching_of_boundary_edge ω n hb1 hb2 hbne hopen hnotrif
  exact ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, Or.inr hRne, hData⟩


















namespace Bc51Witness





def catE (a b : Fin 6) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨      
  (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨      
  (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
  (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) ∨      
  (a = 1 ∧ b = 5) ∨ (a = 5 ∧ b = 1)

instance : DecidableRel catE := fun a b => by unfold catE; infer_instance

def catG : SimpleGraph (Fin 6) := SimpleGraph.fromRel catE
instance : DecidableRel catG.Adj := by unfold catG fromRel; intro a b; infer_instance



theorem catG_isTree : catG.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide





theorem catG_leafCount :
    (univ.filter (fun v => 3 ≤ catG.degree v)).card = 2 ∧
    (univ.filter (fun v => catG.degree v = 1)).card = 4 := by
  constructor <;> decide





theorem catG_internal_lt_leaves :
    (univ.filter (fun v => 3 ≤ catG.degree v)).card
      < (univ.filter (fun v => catG.degree v = 1)).card :=
  flc2_tree_internal_lt_leaves catG catG_isTree (by decide)


def cycleE (a b : Fin 6) : Prop := catE a b ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2)
instance : DecidableRel cycleE := fun a b => by unfold cycleE; infer_instance

def cycleG : SimpleGraph (Fin 6) := SimpleGraph.fromRel cycleE
instance : DecidableRel cycleG.Adj := by unfold cycleG fromRel; intro a b; infer_instance






theorem cycleG_not_acyclic : ¬ cycleG.IsAcyclic := by
  
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





theorem catG_subgraph_acyclic {H : SimpleGraph (Fin 6)} (hsub : H ≤ catG) : H.IsAcyclic :=
  bc51_subgraph_isAcyclic hsub catG_isTree.isAcyclic

end Bc51Witness








theorem bc51_forestCover_nonvacuous_nilWalk {x a : Site d}
    {ω : ConfigSpace (Sym2 (Site d))} (T : SimpleGraph (Site d))
    (hax : a ≠ x) :
    let w : (openSubgraph d (removeSite x ω)).Walk a a := Walk.nil
    x ∉ w.support ∧
      (∀ e, e ∈ (w.mapLe (bc51_openSubgraph_removeSite_le x ω)).edges → e ∈ T.edgeSet) := by
  refine ⟨?_, ?_⟩
  · simpa using (Ne.symm hax)
  · intro e he
    simp only [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.map_nil] at he
    exact absurd he (List.not_mem_nil)





theorem bc51_globalArmForest_nonvacuous_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    bc51_GlobalArmForest ω n :=
  bc51_globalArmForest_star ω n a hsingle hxbox htri hadj habdry hxne hainj hsep
















theorem bc51_burton_keane_bernoulli_of_globalArmForest (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (harm : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc51_GlobalArmForest ω n)
    (hroute : ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc50_burton_keane_bernoulli_of_armForest hd p hp1 hp0
    (fun ω n => bc51_armForestReaching_of_globalArmForest ω n (harm ω n)) hroute

end StatMech.Walls
