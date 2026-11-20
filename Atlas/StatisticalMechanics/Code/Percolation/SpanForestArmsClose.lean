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
import Code.Percolation.BurtonKeaneClose
import Code.Percolation.ForestLeafCountClose
import Code.Percolation.SingleLeafHallClose
import Code.Percolation.BoundaryPruningClose
import Code.Percolation.BKSpanningTreeClose
import Code.Percolation.OpenSpanningForestClose
import Code.Percolation.SecondPeelingClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}








theorem sfa_avoid_no_edge {V : Type*} {T : SimpleGraph V} {x a b : V} (w : T.Walk a b)
    (hx : x ∉ w.support) {e : Sym2 V} (he : e ∈ w.edges) : x ∉ e :=
  fun hxe => hx (w.mem_support_of_mem_edges he hxe)



theorem sfa_avoid_walk {V : Type*} {T : SimpleGraph V} {x a b : V} (ha : a ≠ x) (hb : b ≠ x)
    (h : (T.induce ({x}ᶜ : Set V)).Reachable ⟨a, by simpa using ha⟩ ⟨b, by simpa using hb⟩) :
    ∃ w : T.Walk a b, x ∉ w.support := by
  obtain ⟨w⟩ := h
  set f : (T.induce ({x}ᶜ : Set V)) →g T :=
    { toFun := fun u => (u : V), map_rel' := fun {p q} hpq => hpq } with hf
  set w' := w.map f with hw'
  refine ⟨w', ?_⟩
  intro hx
  rw [hw', Walk.support_map, List.mem_map] at hx
  obtain ⟨⟨y, hy⟩, _, hyx⟩ := hx
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
  exact hy (by simpa [hf] using hyx)






theorem sfa_glue_path {V : Type*} {T : SimpleGraph V} {x c0 c1 z0 z1 : V}
    (hxc0 : T.Adj x c0) (hxc1 : T.Adj x c1)
    (w0 : T.Walk c0 z0) (hw0p : w0.IsPath) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1p : w1.IsPath) (hw1x : x ∉ w1.support)
    (hdisj : ∀ v, v ∈ w0.support → v ∈ w1.support → False) :
    ∃ p : T.Walk z0 z1, p.IsPath ∧ x ∈ p.support ∧ c0 ∈ p.support ∧ c1 ∈ p.support := by
  set tw : T.Walk c0 z1 := Walk.cons hxc0.symm (Walk.cons hxc1 w1) with htw
  set p : T.Walk z0 z1 := w0.reverse.append tw with hp
  have htwsupp : tw.support = c0 :: x :: w1.support := by
    rw [htw, Walk.support_cons, Walk.support_cons]
  have hpsupp : p.support = w0.reverse.support ++ (x :: w1.support) := by
    rw [hp, Walk.support_append, htwsupp]; rfl
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · rw [Walk.isPath_def, hpsupp, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.support_reverse, List.nodup_reverse]; exact hw0p.support_nodup
    · rw [List.nodup_cons]; exact ⟨hw1x, hw1p.support_nodup⟩
    · intro a ha b hb
      rw [Walk.support_reverse, List.mem_reverse] at ha
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact fun h => hw0x (h ▸ ha)
      · exact fun h => hdisj a ha (h ▸ hb)
  · rw [hpsupp, List.mem_append, List.mem_cons]; right; left; rfl
  · rw [hpsupp, List.mem_append]; left; rw [Walk.support_reverse, List.mem_reverse]
    exact w0.start_mem_support
  · rw [hpsupp, List.mem_append, List.mem_cons]; right; right; exact w1.start_mem_support










theorem sfa_walk_avoid_connected (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x a b : Site d} (w : T.Walk a b) (hwx : x ∉ w.support) :
    Connected d (removeSite x ω) a b := by
  classical
  set f : T →g (openSubgraph d ω) :=
    { toFun := id, map_rel' := fun {p q} hpq => hπ p q hpq } with hf
  set ww := w.map f with hww
  have hsupp : x ∉ ww.support := by
    intro hx
    rw [hww, SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [hf] at hyx; subst hyx
    exact hwx hy
  exact slh_walk_avoid_transfer ww hsupp





theorem sfa_armWalks_disjoint (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x c0 c1 z0 z1 : Site d}
    (w0 : T.Walk c0 z0) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1x : x ∉ w1.support)
    (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
    ∀ v, v ∈ w0.support → v ∈ w1.support → False := by
  classical
  intro v hv0 hv1
  apply hcut
  have h0 : Connected d (removeSite x ω) c0 v :=
    sfa_walk_avoid_connected ω T hπ (w0.takeUntil v hv0)
      (fun hx => hw0x (w0.support_takeUntil_subset_support hv0 hx))
  have h1 : Connected d (removeSite x ω) c1 v :=
    sfa_walk_avoid_connected ω T hπ (w1.takeUntil v hv1)
      (fun hx => hw1x (w1.support_takeUntil_subset_support hv1 hx))
  exact h0.trans h1.symm






























open Classical in





def sfa_ArmForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (c : Site d → Fin 3 → Site d) (zr : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d n) ∧
    (∃ v, spc_OnBPath T B v) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      (∀ i, T.Adj x (c x i)) ∧
      (¬ Connected d (removeSite x ω) (c x 0) (c x 1) ∧
       ¬ Connected d (removeSite x ω) (c x 0) (c x 2) ∧
       ¬ Connected d (removeSite x ω) (c x 1) (c x 2)) ∧
      (∀ i, zr x i ∈ B ∧ ∃ w : T.Walk (c x i) (zr x i), x ∉ w.support))












theorem sfa_onBPath_of_arms (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) (B : Set (Site d))
    {x ci cj zi zj : Site d}
    (hxci : T.Adj x ci) (hxcj : T.Adj x cj)
    (wi : T.Walk ci zi) (hwix : x ∉ wi.support) (hzi : zi ∈ B)
    (wj : T.Walk cj zj) (hwjx : x ∉ wj.support) (hzj : zj ∈ B)
    (hcut : ¬ Connected d (removeSite x ω) ci cj) :
    spc_OnBPath T B x ∧ spc_OnBPath T B ci ∧ spc_OnBPath T B cj := by
  classical
  
  have hzne : zi ≠ zj := by
    intro h; subst h; apply hcut
    exact (sfa_walk_avoid_connected ω T hπ wi hwix).trans
      (sfa_walk_avoid_connected ω T hπ wj hwjx).symm
  
  set pi : T.Walk ci zi := (wi.toPath : T.Walk ci zi) with hpi
  set pj : T.Walk cj zj := (wj.toPath : T.Walk cj zj) with hpj
  have hpix : x ∉ pi.support := fun h => hwix (wi.support_toPath_subset h)
  have hpjx : x ∉ pj.support := fun h => hwjx (wj.support_toPath_subset h)
  have hdisj : ∀ v, v ∈ pi.support → v ∈ pj.support → False := by
    have := sfa_armWalks_disjoint ω T hπ pi hpix pj hpjx hcut
    exact this
  
  obtain ⟨p, hpp, hxp, hcip, hcjp⟩ :=
    sfa_glue_path hxci hxcj pi (wi.toPath).2 hpix pj (wj.toPath).2 hpjx hdisj
  refine ⟨⟨zi, zj, hzi, hzj, hzne, p, hpp, hxp⟩,
    ⟨zi, zj, hzi, hzj, hzne, p, hpp, hcip⟩,
    ⟨zi, zj, hzi, hzj, hzne, p, hpp, hcjp⟩⟩






theorem sfa_spanForestArms_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) : spc_SpanForestArms ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ := h
  refine ⟨Vall, T, hTdec, B, c, hTac, hTopen, hTsupp, hBbd, hRne, ?_⟩
  intro x hxbox htri
  obtain ⟨hadj, hcut, hreach⟩ := hData x hxbox htri
  
  obtain ⟨hcut01, hcut02, hcut12⟩ := hcut
  
  have hne01 : c x 0 ≠ c x 1 := fun h => hcut01 (h ▸ connected_refl _ _)
  have hne02 : c x 0 ≠ c x 2 := fun h => hcut02 (h ▸ connected_refl _ _)
  have hne12 : c x 1 ≠ c x 2 := fun h => hcut12 (h ▸ connected_refl _ _)
  
  obtain ⟨hz0, w0, hw0x⟩ := hreach 0
  obtain ⟨hz1, w1, hw1x⟩ := hreach 1
  obtain ⟨hz2, w2, hw2x⟩ := hreach 2
  
  obtain ⟨hxsurv, hc0surv, hc1surv⟩ :=
    sfa_onBPath_of_arms ω T hTopen B (hadj 0) (hadj 1) w0 hw0x hz0 w1 hw1x hz1 hcut01
  obtain ⟨_, _, hc2surv⟩ :=
    sfa_onBPath_of_arms ω T hTopen B (hadj 0) (hadj 2) w0 hw0x hz0 w2 hw2x hz2 hcut02
  refine ⟨hxsurv, ⟨hne01, hne02, hne12⟩, ?_, hcut01, hcut02, hcut12⟩
  intro i
  refine ⟨hadj i, ?_⟩
  fin_cases i
  · exact hc0surv
  · exact hc1surv
  · exact hc2surv




theorem sfa_Tcount_le_boundary_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  spc_Tcount_le_boundary_of_spanForestArms ω n (sfa_spanForestArms_of_armForestReaching ω n h)







open Classical in

theorem sfa_armForestReaching_of_boundary_edge (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {b₁ b₂ : Site d} (hb1 : b₁ ∈ vertexBoundary d n) (hb2 : b₂ ∈ vertexBoundary d n)
    (hbne : b₁ ≠ b₂) (hopen : (openSubgraph d ω).Adj b₁ b₂)
    (hnotrif : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    sfa_ArmForestReaching ω n := by
  classical
  set T : SimpleGraph (Site d) := SimpleGraph.fromEdgeSet {s(b₁, b₂)} with hT
  have hTb : T.Adj b₁ b₂ := by rw [hT, fromEdgeSet_adj]; exact ⟨by simp, hbne⟩
  have hTac : T.IsAcyclic := by
    rw [hT, isAcyclic_iff_forall_adj_isBridge]
    intro u v huv
    rw [fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rw [isBridge_iff]
    refine ⟨by rw [fromEdgeSet_adj]; exact ⟨by simp [hmem], hne⟩, ?_⟩
    intro hreach
    obtain ⟨w⟩ := hreach
    have hbot : ((SimpleGraph.fromEdgeSet {s(b₁, b₂)}).deleteEdges {s(u, v)}) = ⊥ := by
      ext a b
      rw [deleteEdges_adj]
      simp only [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff, bot_adj, iff_false, not_and]
      rintro ⟨hab, habne⟩ hnab
      apply hnab
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        subst_vars <;> tauto
    rw [hbot] at w
    exact hne (w.eq_of_length_eq_zero
      (by cases w with | nil => rfl | cons h _ => exact absurd h (by simp)))
  set B : Set (Site d) := {b₁, b₂} with hB
  set p : T.Walk b₁ b₂ := Walk.cons hTb Walk.nil with hp
  have hpp : p.IsPath := by
    rw [hp, SimpleGraph.Walk.isPath_def]
    change List.Nodup [b₁, b₂]
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, List.nodup_nil, and_true]
    exact ⟨hbne, by trivial⟩
  have honB1 : spc_OnBPath T B b₁ :=
    ⟨b₁, b₂, by simp [hB], by simp [hB], hbne, p, hpp, by simp [hp]⟩
  refine ⟨{b₁, b₂}, T, by rw [hT]; infer_instance, B, fun _ _ => b₁, fun _ _ => b₁, hTac,
    ?_, ?_, ?_, ⟨b₁, honB1⟩, ?_⟩
  · intro u v huv
    rw [hT, fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hopen
    · exact hopen.symm
  · intro u v huv
    rw [hT, fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · rw [hB]; intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  · intro x hxbox htri; exact absurd htri (hnotrif x hxbox)










open Classical in

theorem sfa_armForestReaching_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    sfa_ArmForestReaching ω n := by
  classical
  set lab : Fin 4 → Site d := fun v => match v with
    | 0 => x | 1 => a 0 | 2 => a 1 | 3 => a 2 with hlab
  have hlabinj : Function.Injective lab := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp only [hlab] at huv <;>
      first
        | rfl
        | (exact absurd huv (hxne 0).symm) | (exact absurd huv (hxne 1).symm)
        | (exact absurd huv (hxne 2).symm) | (exact absurd huv.symm (hxne 0).symm)
        | (exact absurd huv.symm (hxne 1).symm) | (exact absurd huv.symm (hxne 2).symm)
        | (exact absurd (hainj huv) (by decide))
  set emb : Fin 4 ↪ Site d := ⟨lab, hlabinj⟩ with hemb
  set T : SimpleGraph (Site d) := SimpleGraph.map emb Flc2Witness.starG with hT
  have hTac : T.IsAcyclic := spc_map_acyclic Flc2Witness.starG_isTree.isAcyclic emb
  have hTadj : ∀ i j : Fin 4, T.Adj (lab i) (lab j) ↔ Flc2Witness.starG.Adj i j := by
    intro i j; rw [hT, SimpleGraph.map_adj]
    constructor
    · rintro ⟨p, q, hpq, h1, h2⟩; exact (hlabinj h1) ▸ (hlabinj h2) ▸ hpq
    · intro h; exact ⟨i, j, h, rfl, rfl⟩
  have hstar : ∀ i : Fin 3, Flc2Witness.starG.Adj 0 i.succ := by
    intro i; rw [Flc2Witness.starG, fromRel_adj]
    refine ⟨(Fin.succ_ne_zero i).symm, ?_⟩
    left; rw [Flc2Witness.starE]; left; exact ⟨rfl, Fin.succ_ne_zero i⟩
  have hlabsucc : ∀ i : Fin 3, lab i.succ = a i := by intro i; fin_cases i <;> rfl
  have hTxai : ∀ i : Fin 3, T.Adj x (a i) := by
    intro i
    have := (hTadj 0 i.succ).mpr (hstar i)
    rwa [show lab 0 = x from rfl, hlabsucc i] at this
  set B : Set (Site d) := {a 0, a 1, a 2} with hB
  have hai_in_B : ∀ i : Fin 3, a i ∈ B := by intro i; fin_cases i <;> simp [hB]
  
  have hpath01 : ∃ p : T.Walk (a 0) (a 1), p.IsPath ∧ x ∈ p.support := by
    refine ⟨Walk.cons (hTxai 0).symm (Walk.cons (hTxai 1) Walk.nil), ?_, by simp⟩
    rw [SimpleGraph.Walk.isPath_def]
    change List.Nodup [a 0, x, a 1]
    have ha01 : a 0 ≠ a 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hainj h)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
      not_or, and_true]
    exact ⟨⟨hxne 0, ha01⟩, (hxne 1).symm, not_false⟩
  obtain ⟨p01, hp01p, hxp01⟩ := hpath01
  have honB_x : spc_OnBPath T B x :=
    ⟨a 0, a 1, hai_in_B 0, hai_in_B 1, fun h => (by decide : (0 : Fin 3) ≠ 1) (hainj h),
      p01, hp01p, hxp01⟩
  refine ⟨{x, a 0, a 1, a 2}, T, by rw [hT]; infer_instance, B, fun _ => a, fun _ => a, hTac,
    ?_, ?_, ?_, ⟨x, honB_x⟩, ?_⟩
  · 
    intro u v huv
    rw [hT, SimpleGraph.map_adj] at huv
    obtain ⟨p, q, hpq, rfl, rfl⟩ := huv
    rw [Flc2Witness.starG, fromRel_adj] at hpq
    obtain ⟨hpqne, hor⟩ := hpq
    change (openSubgraph d ω).Adj (lab p) (lab q)
    fin_cases p <;> fin_cases q <;> simp only [hlab] <;>
      first
        | (exfalso; revert hor; simp only [Flc2Witness.starE]; decide)
        | exact hadj 0 | exact hadj 1 | exact hadj 2
        | exact (hadj 0).symm | exact (hadj 1).symm | exact (hadj 2).symm
  · 
    intro u v huv
    rw [hT, SimpleGraph.map_adj] at huv
    obtain ⟨p, q, hpq, rfl, rfl⟩ := huv
    fin_cases p <;>
      simp only [Finset.mem_insert, Finset.mem_singleton,
        show (emb : Fin 4 → Site d) = lab from rfl] <;>
      first
        | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) | (right; right; right; rfl)
  · 
    rw [hB]; intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact habdry 0
    · exact habdry 1
    · exact habdry 2
  · 
    intro y hybox htri
    have hyx : y = x := hsingle y hybox htri; subst hyx
    refine ⟨fun i => hTxai i, hsep, ?_⟩
    intro i
    refine ⟨hai_in_B i, Walk.nil, ?_⟩
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact fun h => (hxne i) h.symm

end Percolation

end StatMech
