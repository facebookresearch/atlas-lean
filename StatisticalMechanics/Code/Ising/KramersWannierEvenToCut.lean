/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Ising.KramersWannierGeneral

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Ising







section CutParity

variable {V : Type*} [DecidableEq V] (Gp : SimpleGraph V) (δ : Finset (Sym2 V))



def walkParity : {x y : V} → Gp.Walk x y → Bool
  | _, _, .nil => false
  | _, _, .cons (u := u) (v := v) _ p => (decide (s(u, v) ∈ δ)).xor (walkParity p)

@[simp] theorem walkParity_nil {x : V} : walkParity Gp δ (.nil : Gp.Walk x x) = false := rfl

@[simp] theorem walkParity_cons {u v w : V} (h : Gp.Adj u v) (p : Gp.Walk v w) :
    walkParity Gp δ (.cons h p) = (decide (s(u, v) ∈ δ)).xor (walkParity Gp δ p) := rfl

variable {Gp δ}


theorem walkParity_append {x y z : V} (p : Gp.Walk x y) (q : Gp.Walk y z) :
    walkParity Gp δ (p.append q) = (walkParity Gp δ p).xor (walkParity Gp δ q) := by
  induction p with
  | nil => simp
  | cons h p ih => simp [SimpleGraph.Walk.cons_append, ih]


theorem walkParity_reverse {x y : V} (p : Gp.Walk x y) :
    walkParity Gp δ p.reverse = walkParity Gp δ p := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, walkParity_append, ih, walkParity_cons,
      show walkParity Gp δ (SimpleGraph.Walk.cons h p)
        = (decide (s(u, v) ∈ δ)).xor (walkParity Gp δ p) from rfl]
    
    have hedge : s(v, u) = s(u, v) := Sym2.eq_swap
    rw [walkParity_nil, hedge, Bool.xor_false]
    cases walkParity Gp δ p <;> cases hb : decide (s(u, v) ∈ δ) <;> simp [Bool.xor_comm]



@[simp] theorem walkParity_singleton {x y : V} (h : Gp.Adj x y) :
    walkParity Gp δ (SimpleGraph.Walk.cons h (.nil : Gp.Walk y y)) = decide (s(x, y) ∈ δ) := by
  simp

end CutParity








section ParityConfig

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp : SimpleGraph V) [DecidableRel Gp.Adj] (δ : Finset (Sym2 V))





def EvenOnCycles : Prop := ∀ (x : V) (p : Gp.Walk x x), walkParity Gp δ p = false

variable {Gp δ}

omit [Fintype V] [DecidableRel Gp.Adj] in



theorem walkParity_eq_of_evenOnCycles (hev : EvenOnCycles Gp δ) {x y : V}
    (p q : Gp.Walk x y) : walkParity Gp δ p = walkParity Gp δ q := by
  
  have hclosed : walkParity Gp δ (p.append q.reverse) = false := hev _ _
  rw [walkParity_append, walkParity_reverse] at hclosed
  
  revert hclosed
  cases walkParity Gp δ p <;> cases walkParity Gp δ q <;> simp

variable (Gp δ) in



noncomputable def parityConfig (hG : Gp.Preconnected) (v₀ : V) : ConfigSpace V :=
  fun v => walkParity Gp δ (hG v₀ v).some

omit [Fintype V] [DecidableRel Gp.Adj] in




theorem parityConfig_adj_xor (hev : EvenOnCycles Gp δ) (hG : Gp.Preconnected) (v₀ : V)
    {x y : V} (h : Gp.Adj x y) :
    (parityConfig Gp δ hG v₀ x).xor (parityConfig Gp δ hG v₀ y) = decide (s(x, y) ∈ δ) := by
  
  let px : Gp.Walk v₀ x := (hG v₀ x).some
  let walkVy : Gp.Walk v₀ y := px.append (SimpleGraph.Walk.cons h (.nil : Gp.Walk y y))
  have hpar : parityConfig Gp δ hG v₀ y = walkParity Gp δ walkVy := by
    unfold parityConfig
    exact walkParity_eq_of_evenOnCycles hev (hG v₀ y).some walkVy
  have hwalkVy : walkParity Gp δ walkVy
      = (parityConfig Gp δ hG v₀ x).xor (decide (s(x, y) ∈ δ)) := by
    rw [walkParity_append, walkParity_singleton]
    rfl
  rw [hpar, hwalkVy]
  
  cases parityConfig Gp δ hG v₀ x <;>
    cases hb : decide (s(x, y) ∈ δ) <;> simp








theorem cutEdges_parityConfig (hev : EvenOnCycles Gp δ) (hG : Gp.Preconnected) (v₀ : V)
    (hδ : δ ⊆ Gp.edgeFinset) :
    cutEdges Gp (parityConfig Gp δ hG v₀) = δ := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    constructor
    · 
      intro he
      have hadj : Gp.Adj x y := by
        rw [cutEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact he.1
      have hne : (parityConfig Gp δ hG v₀) x ≠ (parityConfig Gp δ hG v₀) y :=
        (mem_cutEdges_iff Gp _ hadj).mp he
      
      have hxor : (parityConfig Gp δ hG v₀ x).xor (parityConfig Gp δ hG v₀ y) = true := by
        cases hx : parityConfig Gp δ hG v₀ x <;> cases hy : parityConfig Gp δ hG v₀ y <;>
          simp_all
      rw [parityConfig_adj_xor hev hG v₀ hadj] at hxor
      exact of_decide_eq_true hxor
    · 
      intro he
      have hadj : Gp.Adj x y := by
        have := hδ he
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      rw [mem_cutEdges_iff Gp _ hadj]
      have hxor := parityConfig_adj_xor hev hG v₀ hadj
      rw [decide_eq_true (by exact he)] at hxor
      
      cases hx : parityConfig Gp δ hG v₀ x <;> cases hy : parityConfig Gp δ hG v₀ y <;>
        simp_all




theorem mem_cutSpace_of_evenOnCycles [Nonempty V] (hG : Gp.Preconnected)
    (hδ : δ ⊆ Gp.edgeFinset) (hev : EvenOnCycles Gp δ) :
    δ ∈ cutSpace Gp := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  rw [cutSpace, Finset.mem_image]
  exact ⟨parityConfig Gp δ hG v₀, Finset.mem_univ _, cutEdges_parityConfig hev hG v₀ hδ⟩

end ParityConfig











section Reduction

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]










def CycleParityCompatible (Gp : SimpleGraph V) [DecidableRel Gp.Adj]
    (ψ : Sym2 V ≃ Sym2 V) (F : Finset (Sym2 V)) : Prop :=
  EvenOnCycles Gp (F.image ψ.symm)

omit [Fintype V] [DecidableRel Gp.Adj] in


theorem mem_image_symm_iff (ψ : Sym2 V ≃ Sym2 V) (F : Finset (Sym2 V)) (e : Sym2 V) :
    e ∈ F.image ψ.symm ↔ ψ e ∈ F := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩; rwa [Equiv.apply_symm_apply]
  · intro he; exact ⟨ψ e, he, ψ.symm_apply_apply e⟩

omit [Fintype V] [DecidableRel Gp.Adj] in




theorem walkParity_image_symm (ψ : Sym2 V ≃ Sym2 V) (F : Finset (Sym2 V))
    {x y : V} (p : Gp.Walk x y) :
    walkParity Gp (F.image ψ.symm) p
      = (p.darts.map (fun d => decide (ψ s(d.fst, d.snd) ∈ F))).foldr Bool.xor false := by
  induction p with
  | nil => simp [walkParity]
  | @cons u v w h q ih =>
    rw [walkParity_cons, ih, SimpleGraph.Walk.darts_cons]
    simp only [List.map_cons, List.foldr_cons]
    congr 1
    rw [decide_eq_decide]
    exact mem_image_symm_iff ψ F s(u, v)






theorem image_symm_subset_edgeFinset (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    {F : Finset (Sym2 V)} (hF : F ⊆ Gd.edgeFinset) :
    F.image ψ.symm ⊆ Gp.edgeFinset := by
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨g, hg, rfl⟩ := he
  exact hsymm g (hF hg)







theorem even_to_cut_of_cycleParity [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hcyc : ∀ F ∈ evenSubgraphs Gd, CycleParityCompatible Gp ψ F) :
    ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp := by
  intro F hF
  have hFsub : F ⊆ Gd.edgeFinset := by
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hF
    exact hF.1
  exact mem_cutSpace_of_evenOnCycles hG
    (image_symm_subset_edgeFinset ψ hsymm hFsub) (hcyc F hF)









noncomputable def edgeCrossing_of_cycleParity [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hedge : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hfwd : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ))
    (hcyc : ∀ F ∈ evenSubgraphs Gd, CycleParityCompatible Gp ψ F) :
    EdgeCrossing Gp Gd where
  ψ := ψ
  edge_mem := hedge
  cut_to_even := hfwd
  even_to_cut := even_to_cut_of_cycleParity hG ψ hsymm hcyc










section Additivity

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V} {δ₁ δ₂ : Finset (Sym2 V)}



theorem walkParity_union_disjoint (hdisj : Disjoint δ₁ δ₂) {x y : V} (p : Gp.Walk x y) :
    walkParity Gp (δ₁ ∪ δ₂) p = (walkParity Gp δ₁ p).xor (walkParity Gp δ₂ p) := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
    rw [walkParity_cons, walkParity_cons, walkParity_cons, ih]
    
    have hsplit : decide (s(u, v) ∈ δ₁ ∪ δ₂)
        = (decide (s(u, v) ∈ δ₁)).xor (decide (s(u, v) ∈ δ₂)) := by
      by_cases h1 : s(u, v) ∈ δ₁
      · have h2 : s(u, v) ∉ δ₂ := fun hc => (Finset.disjoint_left.mp hdisj h1) hc
        simp [Finset.mem_union, h1, h2]
      · by_cases h2 : s(u, v) ∈ δ₂ <;> simp [Finset.mem_union, h1, h2]
    rw [hsplit]
    
    cases decide (s(u, v) ∈ δ₁) <;> cases decide (s(u, v) ∈ δ₂) <;>
      cases walkParity Gp δ₁ q <;> cases walkParity Gp δ₂ q <;> rfl




theorem evenOnCycles_union_disjoint (hdisj : Disjoint δ₁ δ₂)
    (h1 : EvenOnCycles Gp δ₁) (h2 : EvenOnCycles Gp δ₂) :
    EvenOnCycles Gp (δ₁ ∪ δ₂) := by
  intro x p
  rw [walkParity_union_disjoint hdisj p, h1 x p, h2 x p]
  rfl


theorem walkParity_empty (Gp : SimpleGraph V) {x y : V} (p : Gp.Walk x y) :
    walkParity Gp (∅ : Finset (Sym2 V)) p = false := by
  induction p with
  | nil => rfl
  | cons h q ih => rw [walkParity_cons, ih]; simp


theorem evenOnCycles_empty (Gp : SimpleGraph V) : EvenOnCycles Gp (∅ : Finset (Sym2 V)) :=
  fun _ p => walkParity_empty Gp p

end Additivity










section Decomposition

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}






theorem evenOnCycles_biUnion {ι : Type*} (s : Finset ι)
    (pieces : ι → Finset (Sym2 V))
    (hdisj : (s : Set ι).PairwiseDisjoint pieces)
    (hpieces : ∀ i ∈ s, EvenOnCycles Gp (pieces i)) :
    EvenOnCycles Gp (s.biUnion pieces) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have : (∅ : Finset ι).biUnion pieces = (∅ : Finset (Sym2 V)) := by simp
    rw [this]; exact evenOnCycles_empty Gp
  | @insert a s ha ih =>
    have hdisj_a : Disjoint (pieces a) (s.biUnion pieces) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdisj (Finset.mem_insert_self a s)
        (Finset.mem_insert_of_mem hi) (by rintro rfl; exact ha hi)
    have hrest : EvenOnCycles Gp (s.biUnion pieces) :=
      ih (hdisj.subset (by intro i hi; exact Finset.mem_insert_of_mem hi))
        (fun i hi => hpieces i (Finset.mem_insert_of_mem hi))
    have hunion : EvenOnCycles Gp (pieces a ∪ s.biUnion pieces) :=
      evenOnCycles_union_disjoint hdisj_a (hpieces a (Finset.mem_insert_self a s)) hrest
    rw [Finset.biUnion_insert]
    exact hunion

end Decomposition

















section SingleCycle

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]











def SingleDualCycleParity (Gp : SimpleGraph V) [DecidableRel Gp.Adj]
    (ψ : Sym2 V ≃ Sym2 V) (cycleSets : Finset (Sym2 V) → Prop) : Prop :=
  ∀ C : Finset (Sym2 V), cycleSets C → EvenOnCycles Gp (C.image ψ.symm)

omit [Fintype V] in








theorem cycleParityCompatible_of_decomposition (ψ : Sym2 V ≃ Sym2 V)
    {cycleSets : Finset (Sym2 V) → Prop} (hsingle : SingleDualCycleParity Gp ψ cycleSets)
    {F : Finset (Sym2 V)} {ι : Type*} (s : Finset ι)
    (pieces : ι → Finset (Sym2 V))
    (hcov : F = s.biUnion pieces)
    (hdisj : (s : Set ι).PairwiseDisjoint pieces)
    (hcyc : ∀ i ∈ s, cycleSets (pieces i)) :
    CycleParityCompatible Gp ψ F := by
  classical
  change EvenOnCycles Gp (F.image ψ.symm)
  rw [hcov]
  
  have himg : (s.biUnion pieces).image ψ.symm
      = s.biUnion (fun i => (pieces i).image ψ.symm) := Finset.biUnion_image
  rw [himg]
  refine evenOnCycles_biUnion s (fun i => (pieces i).image ψ.symm) ?_ ?_
  · 
    intro i hi j hj hij
    have hd := hdisj hi hj hij
    
    apply Finset.disjoint_left.mpr
    intro e hei hej
    rw [Finset.mem_image] at hei hej
    obtain ⟨a, ha, rfl⟩ := hei
    obtain ⟨b, hb, hba⟩ := hej
    have hab : a = b := ψ.symm.injective hba.symm
    subst hab
    exact (Finset.disjoint_left.mp hd ha) hb
  · intro i hi
    exact hsingle (pieces i) (hcyc i hi)

end SingleCycle











section ClosedWalk

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]









def ClosedDualWalkParity (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj]
    (ψ : Sym2 V ≃ Sym2 V) : Prop :=
  ∀ {w : V} (W : Gd.Walk w w), EvenOnCycles Gp ((W.edges.toFinset).image ψ.symm)








def EvenSubgraphWalkDecomp (Gd : SimpleGraph V) [DecidableRel Gd.Adj] : Prop :=
  ∀ F ∈ evenSubgraphs Gd, ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι)
      (w : ι → V) (W : (i : ι) → Gd.Walk (w i) (w i)),
    F = s.biUnion (fun i => (W i).edges.toFinset) ∧
    (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset)







theorem even_to_cut_of_closedWalkParity [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hdecomp : EvenSubgraphWalkDecomp Gd)
    (hlink : ClosedDualWalkParity Gp Gd ψ) :
    ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp := by
  refine even_to_cut_of_cycleParity hG ψ hsymm ?_
  intro F hF
  obtain ⟨ι, _hιdec, s, w, W, hcov, hdisj⟩ := hdecomp F hF
  
  have hsingle : SingleDualCycleParity Gp ψ
      (fun C => ∃ (z : V) (Wz : Gd.Walk z z), C = Wz.edges.toFinset) := by
    rintro C ⟨z, Wz, rfl⟩
    exact hlink Wz
  exact cycleParityCompatible_of_decomposition ψ hsingle s
    (fun i => (W i).edges.toFinset) hcov hdisj (fun i _ => ⟨w i, W i, rfl⟩)












noncomputable def edgeCrossing_of_closedWalkParity [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hedge : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hfwd : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ))
    (hdecomp : EvenSubgraphWalkDecomp Gd)
    (hlink : ClosedDualWalkParity Gp Gd ψ) :
    EdgeCrossing Gp Gd where
  ψ := ψ
  edge_mem := hedge
  cut_to_even := hfwd
  even_to_cut := even_to_cut_of_closedWalkParity hG ψ hsymm hdecomp hlink









omit [Fintype V] [DecidableEq V] [DecidableRel Gd.Adj] in


theorem edges_eq_nil_of_isEmpty_edgeSet {w : V} (hGd : Gd.edgeSet = ∅)
    (W : Gd.Walk w w) : W.edges = [] := by
  cases W with
  | nil => rfl
  | cons h _ =>
    exact absurd (Gd.mem_edgeSet.mpr h) (by rw [hGd]; exact id)

omit [Fintype V] [DecidableRel Gd.Adj] in




theorem closedDualWalkParity_of_edgeless (ψ : Sym2 V ≃ Sym2 V) (hGd : Gd.edgeSet = ∅) :
    ClosedDualWalkParity Gp Gd ψ := by
  intro w W
  have hnil : W.edges = [] := edges_eq_nil_of_isEmpty_edgeSet hGd W
  have hempty : (W.edges.toFinset).image ψ.symm = (∅ : Finset (Sym2 V)) := by
    rw [hnil]; simp
  rw [hempty]
  exact evenOnCycles_empty Gp

end ClosedWalk

end Reduction

end Ising

end StatMech
