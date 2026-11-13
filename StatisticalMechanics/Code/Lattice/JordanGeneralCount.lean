/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.PlanarFaceGeometric
import Code.Lattice.JordanEnclosure
import Code.Lattice.EulerFaces2
import Code.Lattice.EulerGeneral
import Code.Lattice.JordanEulerInduction
import Code.Lattice.WhitneyBridge
import Code.Lattice.JordanEvenClose
import Code.Lattice.JordanEvenBiconditional
import Code.Lattice.JordanFaithfulCount
import Code.Lattice.JordanVeblenStep
import Code.Lattice.JordanVeblenPeel
import Code.Lattice.JordanIsCyclesCount

open SimpleGraph Set

namespace StatMech

namespace Lattice









theorem jgc_leaf_deleteEdges_isolated {V : Type*} {K : SimpleGraph V} {x z : V}
    (huniq : ∀ w, K.Adj x w → w = z) :
    ∀ w, ¬ (K.deleteEdges {s(x, z)}).Adj x w := by
  intro w hadjw
  rw [deleteEdges_adj] at hadjw
  obtain ⟨hKxw, hnotin⟩ := hadjw
  have hwz : w = z := huniq w hKxw
  subst hwz
  exact hnotin (by rw [Set.mem_singleton_iff])




theorem jgc_leaf_not_reachable {V : Type*} {K : SimpleGraph V} {x z : V} (hadj : K.Adj x z)
    (huniq : ∀ w, K.Adj x w → w = z) :
    ¬ (K.deleteEdges {s(x, z)}).Reachable x z := by
  have hxz : x ≠ z := K.ne_of_adj hadj
  rintro ⟨wk⟩
  have hxiso := jgc_leaf_deleteEdges_isolated huniq
  cases wk with
  | nil => exact hxz rfl
  | cons hh _ => exact hxiso _ hh




theorem jgc_faceCount_deleteLeaf {V : Type*} [Finite V] [DecidableEq V] (K : SimpleGraph V)
    {x z : V} (hadj : K.Adj x z) (huniq : ∀ w, K.Adj x w → w = z) :
    faceCount (K.deleteEdges {s(x, z)}) = faceCount K := by
  classical
  have hmem : s(x, z) ∈ K.edgeSet := by rwa [SimpleGraph.mem_edgeSet]
  exact (faceCount_deleteEdges_of_isBridge K hmem (jgc_leaf_not_reachable hadj huniq)).1

















theorem jgc_tc_deleteLeaf (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (hKle : K ≤ P.G)
    {x z : P.V} (hadj : K.Adj x z) (huniq : ∀ w, K.Adj x w → w = z) :
    jic_tc P (K.deleteEdges {s(x, z)}) = jic_tc P K := by
  classical
  set K' := K.deleteEdges {s(x, z)} with hK'
  have hmem : s(x, z) ∈ K.edgeSet := by rwa [SimpleGraph.mem_edgeSet]
  have hKeq : K = K' ⊔ edge x z := deleteEdges_sup_edge_eq K x z hmem
  have hxz : x ≠ z := K.ne_of_adj hadj
  
  have hiso : ∀ w, ¬ K'.Adj x w := jgc_leaf_deleteEdges_isolated huniq
  
  have hlat : (hypercubicLattice 2).Adj (P.emb x) (P.emb z) := P.isSub (hKle hadj)
  
  have hkeep := jic_tc_sup_edge_keep P K' hxz hlat hiso
  rw [hKeq, hkeep]
























inductive jgc_IsCactus {V : Type*} : SimpleGraph V → Prop where
  | bot : jgc_IsCactus (⊥ : SimpleGraph V)
  | leaf {K : SimpleGraph V} {x z : V} (hadj : K.Adj x z) (huniq : ∀ w, K.Adj x w → w = z)
      (hrec : jgc_IsCactus (K.deleteEdges {s(x, z)})) : jgc_IsCactus K
  | cycle {K : SimpleGraph V} (hcyc : K.IsCycles) {v : V} (p : K.Walk v v) (hp : p.IsCycle)
      (hrec : jgc_IsCactus (K.deleteEdges p.toSubgraph.edgeSet)) : jgc_IsCactus K

















theorem jgc_tc_eq_faceCount (P : PlanarZ2Subgraph) :
    ∀ {K : SimpleGraph P.V}, jgc_IsCactus K → K ≤ P.G → jic_tc P K = faceCount K := by
  classical
  haveI : Finite P.V := P.finV
  haveI : DecidableEq P.V := P.decV
  intro K hcac
  induction hcac with
  | bot =>
    intro _
    
    unfold jic_tc
    rw [jei_pushGraph_bot, jfc_whb_bot]
    have hlat : Nat.card (hypercubicLattice 2).ConnectedComponent = 1 := by
      have hreach : ∀ a b : Site 2, (hypercubicLattice 2).Reachable a b :=
        fun a b => pbs_reach_all a b
      have hsub : Subsingleton (hypercubicLattice 2).ConnectedComponent :=
        ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hreach a b))⟩
      haveI : Nonempty (hypercubicLattice 2).ConnectedComponent :=
        ⟨(hypercubicLattice 2).connectedComponentMk ![0, 0]⟩
      rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, inferInstance⟩
    rw [hlat]
    unfold faceCount nullity
    rw [SimpleGraph.edgeSet_bot, Set.ncard_empty, card_components_bot]; simp
  | @leaf K x z hadj huniq hrec ih =>
    intro hKle
    
    have hK'le : K.deleteEdges {s(x, z)} ≤ P.G := (deleteEdges_le _).trans hKle
    have ihK' := ih hK'le
    rw [← jgc_tc_deleteLeaf P K hKle hadj huniq, ihK', jgc_faceCount_deleteLeaf K hadj huniq]
  | @cycle K hcyc v p hp hrec ih =>
    intro hKle
    haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
    have hK'le : K.deleteEdges p.toSubgraph.edgeSet ≤ P.G := (deleteEdges_le _).trans hKle
    have ihK' := ih hK'le
    
    have hreg := jic_tc_deleteCycle P K hKle hcyc p hp
    have hface := jvp_faceCount_deleteCycle K hcyc p hp
    rw [hreg, ihK']; omega



theorem jgc_total_count (P : PlanarZ2Subgraph) (hcac : jgc_IsCactus P.G) :
    Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
  have h := jgc_tc_eq_faceCount P hcac le_rfl
  unfold jic_tc at h
  rwa [jei_pushGraph_G P] at h



theorem jgc_faithfulRegionCount_eq_nullity (P : PlanarZ2Subgraph) (hcac : jgc_IsCactus P.G) :
    whc_faithfulRegionCount P = nullity P.G := by
  have htot := jgc_total_count P hcac
  have hcard := jfc_whb_bounded_add_one_eq_card P
  rw [htot, faceCount] at hcard
  omega











theorem jgc_faithfulDiscreteJordan (P : PlanarZ2Subgraph) (hcac : jgc_IsCactus P.G) :
    whc_FaithfulDiscreteJordan P := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)
  have heq : whc_faithfulRegionCount P = nullity P.G :=
    jgc_faithfulRegionCount_eq_nullity P hcac
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩









theorem jgc_isCactus_of_isCycles {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) (hcyc : K.IsCycles) : jgc_IsCactus K := by
  classical
  haveI : Fintype V := Fintype.ofFinite _
  generalize hn : K.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      have hempty : K.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite K.edgeSet)).mp hn
      have hbot : K = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot; exact jgc_IsCactus.bot
    · have hne : K.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hne
      obtain ⟨a, b⟩ := e
      rw [SimpleGraph.mem_edgeSet] at he
      have hnbr : (K.neighborSet a).Nonempty := ⟨b, he⟩
      obtain ⟨p, hpc, _⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
        (v := a) (c := K.connectedComponentMk a) rfl hnbr
      have hK'cyc : (K.deleteEdges p.toSubgraph.edgeSet).IsCycles :=
        jvp_isCycles_deleteCycle_isCycles hcyc p hpc
      have hlt : (K.deleteEdges p.toSubgraph.edgeSet).edgeSet.ncard < K.edgeSet.ncard :=
        jvp_ncard_deleteCycle_lt p hpc
      refine jgc_IsCactus.cycle hcyc p hpc (ih _ (by omega) _ hK'cyc rfl)





theorem jgc_isCactus_of_isAcyclic {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) (hacyc : K.IsAcyclic) : jgc_IsCactus K := by
  classical
  haveI : Fintype V := Fintype.ofFinite _
  generalize hn : K.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    haveI hdec : DecidableRel K.Adj := Classical.decRel _
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      have hempty : K.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite K.edgeSet)).mp hn
      have hbot : K = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot; exact jgc_IsCactus.bot
    · have hne : K.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      
      
      obtain ⟨e, he⟩ := hne
      obtain ⟨a, b⟩ := e
      rw [SimpleGraph.mem_edgeSet] at he
      
      set C := K.connectedComponentMk a with hC
      set s : Set V := (C.supp : Set V) with hs
      haveI : Fintype ↥s := Fintype.ofFinite _
      haveI : DecidableRel (K.induce s).Adj := Classical.decRel _
      have has : a ∈ s := by rw [hs, SimpleGraph.ConnectedComponent.mem_supp_iff, hC]
      have hbs : b ∈ s := by
        rw [hs, SimpleGraph.ConnectedComponent.mem_supp_iff, hC, SimpleGraph.ConnectedComponent.eq]
        exact he.symm.reachable
      have hGs_conn : (K.induce s).Connected := C.connected_toSimpleGraph
      have hGs_acyc : (K.induce s).IsAcyclic := hacyc.induce _
      have hGs_tree : (K.induce s).IsTree := ⟨hGs_conn, hGs_acyc⟩
      haveI : Nontrivial ↥s :=
        ⟨⟨⟨a, has⟩, ⟨b, hbs⟩, fun h => K.ne_of_adj he (Subtype.ext_iff.mp h)⟩⟩
      obtain ⟨u, hu⟩ := hGs_tree.exists_vert_degree_one_of_nontrivial
      
      have hsub : K.neighborSet ↑u ⊆ s := jeb_neighborSet_subset_component K C u
      have hdeg : (K.induce s).degree u = K.degree ↑u := jeb_degree_induce_eq' K s u hsub
      have hone : K.degree ↑u = 1 := hdeg ▸ hu
      
      rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_one] at hone
      obtain ⟨z, hz⟩ := hone
      have hadjuz : K.Adj ↑u z := by
        have : z ∈ K.neighborFinset ↑u := by rw [hz]; exact Finset.mem_singleton_self z
        rwa [SimpleGraph.mem_neighborFinset] at this
      have huniq : ∀ w, K.Adj ↑u w → w = z := by
        intro w hw
        have : w ∈ K.neighborFinset ↑u := by rw [SimpleGraph.mem_neighborFinset]; exact hw
        rw [hz, Finset.mem_singleton] at this; exact this
      
      have hK'acyc : (K.deleteEdges {s(↑u, z)}).IsAcyclic := hacyc.anti (deleteEdges_le _)
      have hmem : s(↑u, z) ∈ K.edgeSet := by rwa [SimpleGraph.mem_edgeSet]
      have hlt : (K.deleteEdges {s(↑u, z)}).edgeSet.ncard < K.edgeSet.ncard := by
        rw [edgeSet_deleteEdges]
        have hssub : K.edgeSet \ {s(↑u, z)} ⊂ K.edgeSet :=
          ⟨Set.diff_subset, fun hcontra => (hcontra hmem).2 rfl⟩
        exact Set.ncard_lt_ncard hssub (Set.toFinite _)
      exact jgc_IsCactus.leaf hadjuz huniq (ih _ (by omega) _ hK'acyc rfl)










def jgc_pend_emb (i : Fin 5) : Site 2 :=
  match i with
  | 0 => ![0, 0] | 1 => ![1, 0] | 2 => ![1, 1] | 3 => ![0, 1] | 4 => ![-1, 0]

theorem jgc_pend_emb_inj : Function.Injective jgc_pend_emb := by decide +kernel


def jgc_pend_rel (i j : Fin 5) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 0) || (i == 1 && j == 2) || (i == 2 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 0) || (i == 0 && j == 3) ||
  (i == 0 && j == 4) || (i == 4 && j == 0)


def jgc_pend_G : SimpleGraph (Fin 5) where
  Adj i j := jgc_pend_rel i j
  symm := by intro i j h; revert h; revert i j; decide
  loopless := ⟨by intro i h; revert h; revert i; decide⟩

@[simp] theorem jgc_pend_G_adj (i j : Fin 5) : jgc_pend_G.Adj i j ↔ jgc_pend_rel i j := Iff.rfl

theorem jgc_pend_isSub : ∀ ⦃i j : Fin 5⦄, jgc_pend_G.Adj i j →
    (hypercubicLattice 2).Adj (jgc_pend_emb i) (jgc_pend_emb j) := by
  intro i j h
  rw [jgc_pend_G_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jgc_pend_rel, jgc_pend_emb]


noncomputable def jgc_pend_P : PlanarZ2Subgraph where
  V := Fin 5
  finV := inferInstance
  decV := inferInstance
  G := jgc_pend_G
  emb := ⟨jgc_pend_emb, jgc_pend_emb_inj⟩
  isSub := jgc_pend_isSub


def jgc_pend_core : SimpleGraph (Fin 5) where
  Adj i j :=
    ((i == 0 && j == 1) || (i == 1 && j == 0) || (i == 1 && j == 2) || (i == 2 && j == 1) ||
     (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 0) || (i == 0 && j == 3) : Bool)
  symm := by intro i j h; revert h; revert i j; decide
  loopless := ⟨by intro i h; revert h; revert i; decide⟩

@[simp] theorem jgc_pend_core_adj (i j : Fin 5) : jgc_pend_core.Adj i j ↔
    ((i == 0 && j == 1) || (i == 1 && j == 0) || (i == 1 && j == 2) || (i == 2 && j == 1) ||
     (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 0) || (i == 0 && j == 3) : Bool) :=
  Iff.rfl


theorem jgc_pend_leaf_uniq : ∀ w, jgc_pend_G.Adj 4 w → w = 0 := by
  intro w h; rw [jgc_pend_G_adj] at h; revert h; fin_cases w <;> simp [jgc_pend_rel]

theorem jgc_pend_leaf_adj : jgc_pend_G.Adj 4 0 := by rw [jgc_pend_G_adj]; decide


theorem jgc_pend_delete_eq_core :
    jgc_pend_G.deleteEdges {s((4 : Fin 5), 0)} = jgc_pend_core := by
  ext i j
  rw [deleteEdges_adj, jgc_pend_G_adj, jgc_pend_core_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  revert i j; decide



theorem jgc_pend_core_isCycles : jgc_pend_core.IsCycles := by
  intro v hv
  rw [Set.ncard_eq_two]
  fin_cases v
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet] <;> decide⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet] <;> decide⟩
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet] <;> decide⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet] <;> decide⟩
  · 
    exfalso
    obtain ⟨w, hw⟩ := hv
    rw [SimpleGraph.mem_neighborSet, jgc_pend_core_adj] at hw
    revert hw; fin_cases w <;> decide



theorem jgc_pend_isCactus : jgc_IsCactus jgc_pend_G := by
  refine jgc_IsCactus.leaf jgc_pend_leaf_adj jgc_pend_leaf_uniq ?_
  rw [jgc_pend_delete_eq_core]
  exact jgc_isCactus_of_isCycles jgc_pend_core jgc_pend_core_isCycles




theorem jgc_pend_not_isCycles : ¬ jgc_pend_G.IsCycles := by
  intro hcyc
  have hv : (jgc_pend_G.neighborSet 0).Nonempty :=
    ⟨1, by rw [SimpleGraph.mem_neighborSet, jgc_pend_G_adj]; decide⟩
  have h2 := hcyc hv
  
  have h3 : jgc_pend_G.neighborSet 0 = {1, 3, 4} := by
    ext w; rw [SimpleGraph.mem_neighborSet, jgc_pend_G_adj]
    fin_cases w <;> simp [jgc_pend_rel]
  rw [h3] at h2
  rw [show ({1, 3, 4} : Set (Fin 5)).ncard = 3 by
    rw [Set.ncard_eq_toFinset_card']; decide] at h2
  exact absurd h2 (by decide)






theorem jgc_faithfulDiscreteJordan_pendantSquare : whc_FaithfulDiscreteJordan jgc_pend_P :=
  jgc_faithfulDiscreteJordan jgc_pend_P jgc_pend_isCactus




























end Lattice

end StatMech
