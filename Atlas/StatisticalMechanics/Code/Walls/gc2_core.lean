/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc2_pairsubconfig
import Code.Walls.gc2_shiftbij
import Code.Walls.gc_subgraphcount

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]
















def gc2_FB (ends : ι → Sym2 V) (M : Finset ι) (B : Finset V) : Prop :=
  ∀ u : V, Even (#((compOf ends M u).filter (fun x => x ∈ B)))



theorem gc2_compOf_eq_of_connK (ends : ι → Sym2 V) (M : Finset ι) {u v : V}
    (h : connK ends M u v) : compOf ends M u = compOf ends M v := by
  ext x
  simp only [mem_compOf]
  exact ⟨fun hux => (connK_symm ends M h).trans hux, fun hvx => h.trans hvx⟩


















theorem gc2_FB_pair_within_cluster (ends : ι → Sym2 V) (M : Finset ι) (B : Finset V)
    (hFB : gc2_FB ends M B) {u : V} (hu : u ∈ B) :
    ∃ v ∈ B, v ≠ u ∧ connK ends M u v := by
  have heven := hFB u
  set S := (compOf ends M u).filter (fun x => x ∈ B) with hS
  have huS : u ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨by rw [mem_compOf]; exact Relation.ReflTransGen.refl, hu⟩
  have hpos : 0 < #S := Finset.card_pos.2 ⟨u, huS⟩
  have hcard : 1 < #S := by
    rcases Nat.lt_or_ge 1 (#S) with h | h
    · exact h
    · have hone : #S = 1 := by omega
      rw [hone] at heven
      exact absurd heven (by decide)
  obtain ⟨v, hvS, hvu⟩ := Finset.exists_mem_ne hcard u
  rw [hS, Finset.mem_filter, mem_compOf] at hvS
  exact ⟨v, hvS.2, hvu, hvS.1⟩


















theorem gc2_FB_remove_pair (ends : ι → Sym2 V) (M : Finset ι) (B : Finset V)
    {u v : V} (huv : u ≠ v) (hu : u ∈ B) (hv : v ∈ B)
    (hconn : connK ends M u v) (hFB : gc2_FB ends M B) :
    gc2_FB ends M (B ∆ {u, v}) := by
  intro w
  
  have hBdiff : B ∆ ({u, v} : Finset V) = B \ {u, v} := by
    rw [symmDiff_def]
    have hempty : ({u, v} : Finset V) \ B = ∅ := by
      rw [Finset.sdiff_eq_empty_iff_subset]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact hu; exact hv]
    rw [hempty]; simp
  rw [hBdiff]
  by_cases hwu : connK ends M w u
  · 
    have hwv : connK ends M w v := hwu.trans hconn
    have key : (compOf ends M w).filter (fun x => x ∈ B \ {u, v})
        = ((compOf ends M w).filter (fun x => x ∈ B)) \ {u, v} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [key]
    have huf : u ∈ (compOf ends M w).filter (fun x => x ∈ B) := by
      rw [Finset.mem_filter, mem_compOf]; exact ⟨hwu, hu⟩
    have hvf : v ∈ (compOf ends M w).filter (fun x => x ∈ B) := by
      rw [Finset.mem_filter, mem_compOf]; exact ⟨hwv, hv⟩
    have hsub : ({u, v} : Finset V) ⊆ (compOf ends M w).filter (fun x => x ∈ B) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact huf; exact hvf]
    have hcard2 : #(({u, v} : Finset V)) = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [huv]), Finset.card_singleton]
    have heven := hFB w
    rw [Finset.card_sdiff_of_subset hsub, hcard2]
    rcases heven with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  · 
    have hwv : ¬ connK ends M w v := fun hwv' => hwu (hwv'.trans (connK_symm ends M hconn))
    have key : (compOf ends M w).filter (fun x => x ∈ B \ {u, v})
        = (compOf ends M w).filter (fun x => x ∈ B) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxc, hxb, _⟩; exact ⟨hxc, hxb⟩
      · rintro ⟨hxc, hxb⟩
        refine ⟨hxc, hxb, ?_⟩
        rw [mem_compOf] at hxc
        rintro (rfl | rfl)
        · exact hwu hxc
        · exact hwv hxc
    rw [key]; exact hFB w




























theorem gc2_minlenDisjoint_K_exists (ends : ι → Sym2 V) (M : Finset ι) :
    ∀ (B : Finset V), gc2_FB ends M B → ∃ K ⊆ M, sources ends K = B := by
  intro B
  induction B using Finset.strongInduction with
  | _ B ih =>
    intro hFB
    rcases B.eq_empty_or_nonempty with hB | hB
    · 
      subst hB
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      ext x; simp [RandomCurrent.sources, degK]
    · 
      obtain ⟨u, hu⟩ := hB
      obtain ⟨v, hv, hvu, hconn⟩ := gc2_FB_pair_within_cluster ends M B hFB hu
      have huv : u ≠ v := fun h => hvu h.symm
      set B' := B ∆ ({u, v} : Finset V) with hB'
      have hFB' : gc2_FB ends M B' := gc2_FB_remove_pair ends M B huv hu hv hconn hFB
      
      have hBdiff : B' = B \ {u, v} := by
        rw [hB', symmDiff_def]
        have hempty : ({u, v} : Finset V) \ B = ∅ := by
          rw [Finset.sdiff_eq_empty_iff_subset]
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> [exact hu; exact hv]
        rw [hempty]; simp
      have hssub : B' ⊂ B := by
        rw [hBdiff]
        refine Finset.sdiff_ssubset ?_ ?_
        · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> [exact hu; exact hv]
        · exact ⟨u, by simp⟩
      obtain ⟨K', hK'M, hK'src⟩ := ih B' hssub hFB'
      
      obtain ⟨P, hPM, hPsrc⟩ := gc2_pair_subconfig ends M hconn huv
      
      refine ⟨K' ∆ P, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_symmDiff] at hx
        rcases hx with ⟨h, _⟩ | ⟨h, _⟩
        · exact hK'M h
        · exact hPM h
      · rw [sources_symmDiff, hK'src, hPsrc, hB', symmDiff_assoc, symmDiff_self, symmDiff_bot]



































theorem gc2_splice_boundary (ends : ι → Sym2 V) (P P' : Finset ι) :
    sources ends (P ∆ P') = sources ends P ∆ sources ends P' :=
  sources_symmDiff ends P P'










theorem gc2_splice_shorter (P P' : Finset ι) {i : ι} (hiP : i ∈ P) (hiP' : i ∈ P') :
    #(P ∆ P') < #P + #P' := by
  have hsub : P ∆ P' ⊆ (P ∪ P').erase i := by
    intro x hx
    rw [Finset.mem_erase]
    rw [Finset.mem_symmDiff] at hx
    refine ⟨?_, ?_⟩
    · rintro rfl; rcases hx with ⟨_, h⟩ | ⟨_, h⟩; exacts [h hiP', h hiP]
    · rw [Finset.mem_union]; rcases hx with ⟨h, _⟩ | ⟨h, _⟩; exacts [Or.inl h, Or.inr h]
  calc #(P ∆ P') ≤ #((P ∪ P').erase i) := Finset.card_le_card hsub
    _ < #(P ∪ P') := Finset.card_erase_lt_of_mem (Finset.mem_union.2 (Or.inl hiP))
    _ ≤ #P + #P' := Finset.card_union_le P P'








theorem gc2_splice_surgery (ends : ι → Sym2 V) (M P P' : Finset ι)
    (hPM : P ⊆ M) (hP'M : P' ⊆ M) {i : ι} (hiP : i ∈ P) (hiP' : i ∈ P') :
    P ∆ P' ⊆ M ∧ sources ends (P ∆ P') = sources ends P ∆ sources ends P'
      ∧ #(P ∆ P') < #P + #P' := by
  refine ⟨?_, gc2_splice_boundary ends P P', gc2_splice_shorter P P' hiP hiP'⟩
  intro x hx
  rw [Finset.mem_symmDiff] at hx
  rcases hx with ⟨h, _⟩ | ⟨h, _⟩
  · exact hPM h
  · exact hP'M h













theorem gc2_Kedge_even_in_Mcomp (ends : ι → Sym2 V) (M K : Finset ι) (hKM : K ⊆ M)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) (w : V) {i : ι} (hi : i ∈ K) :
    Even (#((compOf ends M w).filter (fun x => x ∈ ends i))) := by
  obtain ⟨⟨a, b⟩, hab⟩ := (ends i).exists_rep
  have hiM : i ∈ M := hKM hi
  have hne : a ≠ b := by
    intro h; subst h; exact hnd i hiM (hab ▸ Sym2.mk_isDiag_iff.2 rfl)
  have hset : (compOf ends M w).filter (fun x => x ∈ ends i)
            = (({a, b} : Finset V)).filter (fun x => x ∈ compOf ends M w) := by
    ext x
    simp only [Finset.mem_filter, ← hab, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hset]
  have key : (a ∈ compOf ends M w) ↔ (b ∈ compOf ends M w) := by
    constructor
    · intro ha
      rw [mem_compOf] at ha ⊢
      exact ha.tail ⟨i, hiM, hab ▸ Sym2.mem_mk_left a b, hab ▸ Sym2.mem_mk_right a b, hne⟩
    · intro hb
      rw [mem_compOf] at hb ⊢
      exact hb.tail ⟨i, hiM, hab ▸ Sym2.mem_mk_right a b, hab ▸ Sym2.mem_mk_left a b, hne.symm⟩
  by_cases ha : a ∈ compOf ends M w
  · have hb := key.1 ha
    rw [Finset.filter_insert, Finset.filter_singleton, if_pos ha, if_pos hb,
      Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    exact ⟨1, rfl⟩
  · have hb : b ∉ compOf ends M w := fun h => ha (key.2 h)
    rw [Finset.filter_insert, Finset.filter_singleton, if_neg ha, if_neg hb]; simp











theorem gc2_K_exists_imp_FB (ends : ι → Sym2 V) (M K : Finset ι) (hKM : K ⊆ M)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) {B : Finset V} (hKsrc : sources ends K = B) :
    gc2_FB ends M B := by
  intro w
  subst hKsrc
  
  have hSeq : (compOf ends M w).filter (fun x => x ∈ RandomCurrent.sources ends K)
      = (compOf ends M w).filter (fun x => Odd (degK ends K x)) := by
    apply Finset.filter_congr; intro x _; rw [RandomCurrent.mem_sources]
  rw [hSeq]
  
  have hsum_even : Even (∑ x ∈ compOf ends M w, degK ends K x) := by
    have heq : ∑ x ∈ compOf ends M w, degK ends K x
        = ∑ i ∈ K, #((compOf ends M w).filter (fun x => x ∈ ends i)) := by
      unfold degK
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    rw [heq]
    exact Finset.even_sum _ (fun i hi => gc2_Kedge_even_in_Mcomp ends M K hKM hnd w hi)
  
  exact (even_sum_iff_even_count _ _).1 hsum_even














theorem gc2_count_B_eq_count_empty_of_K (ends : ι → Sym2 V) (M K : Finset ι) (hKM : K ⊆ M)
    {B : Finset V} (hKsrc : sources ends K = B) :
    #(M.powerset.filter (fun N => sources ends N = B))
      = #(M.powerset.filter (fun N => sources ends N = ∅)) := by
  
  have hbij := sources_shift_bijOn ends M K hKM B
  rw [hKsrc, symmDiff_self] at hbij
  have himg : (M.powerset.filter (fun N => sources ends N = ∅))
      = (M.powerset.filter (fun N => sources ends N = B)).image (fun N => N ∆ K) := by
    ext N
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · intro ⟨hNm, hNsrc⟩
      obtain ⟨L, hL, hLN⟩ := hbij.2.2 ⟨hNm, hNsrc⟩
      exact ⟨L, ⟨hL.1, hL.2⟩, hLN⟩
    · rintro ⟨L, ⟨hLm, hLsrc⟩, rfl⟩
      have := hbij.1 ⟨hLm, hLsrc⟩
      exact ⟨this.1, this.2⟩
  rw [himg, Finset.card_image_of_injOn]
  intro K₁ hK₁ K₂ hK₂ h
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hK₁ hK₂
  exact hbij.2.1 ⟨hK₁.1, hK₁.2⟩ ⟨hK₂.1, hK₂.2⟩ h













theorem gc2_eq_swi_count (ends : ι → Sym2 V) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) (B : Finset V) :
    #(M.powerset.filter (fun N => sources ends N = B))
      = (if gc2_FB ends M B then 1 else 0)
          * #(M.powerset.filter (fun N => sources ends N = ∅)) := by
  by_cases hFB : gc2_FB ends M B
  · rw [if_pos hFB, one_mul]
    obtain ⟨K, hKM, hKsrc⟩ := gc2_minlenDisjoint_K_exists ends M B hFB
    exact gc2_count_B_eq_count_empty_of_K ends M K hKM hKsrc
  · rw [if_neg hFB, zero_mul]
    
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro N hNpow hNsrc
    rw [Finset.mem_powerset] at hNpow
    exact hFB (gc2_K_exists_imp_FB ends M N hNpow hnd hNsrc)









open StatMech.Sharpness.FluxEdgeCopy in





theorem gc2_minlenDisjoint_K_exists_current {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ)
    (M : Finset (Copy G m)) (B : Finset W)
    (hFB : gc2_FB (endsM G m) M B) :
    ∃ K ⊆ M, RandomCurrent.sources (endsM G m) K = B :=
  gc2_minlenDisjoint_K_exists (endsM G m) M B hFB

open StatMech.Sharpness.FluxEdgeCopy in










theorem gc2_eq_swi_count_current {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ)
    (M : Finset (Copy G m)) (B : Finset W) :
    #(M.powerset.filter (fun N => RandomCurrent.sources (endsM G m) N = B))
      = (if gc2_FB (endsM G m) M B then 1 else 0)
          * #(M.powerset.filter (fun N => RandomCurrent.sources (endsM G m) N = ∅)) :=
  gc2_eq_swi_count (endsM G m) M (fun i _ => endsM_not_isDiag G m i) B














open StatMech.Sharpness.FluxEdgeCopy in













theorem gc2_eq_swi {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ) (B : Finset W) :
    (∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = B
          then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0))
      = (if gc2_FB (endsM G m) (Finset.univ : Finset (Copy G m)) B then 1 else 0)
        * (∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m},
          (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = ∅
            then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0)) := by
  rw [StatMech.Walls.gc_subgraph_count G m B, StatMech.Walls.gc_subgraph_count G m ∅]
  have huniv : (Finset.univ : Finset (Copy G m)).powerset = Finset.univ := by
    ext N; simp
  have h := gc2_eq_swi_count_current G m (Finset.univ : Finset (Copy G m)) B
  rw [huniv] at h
  exact_mod_cast h

end StatMech.Walls
