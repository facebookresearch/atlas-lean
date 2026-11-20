/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Code.Walls.bc16menger
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]







def bc17_familyMapLe {G G' : SimpleGraph V} (hGG' : G' ≤ G) {A B : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G' A B ι) : bc16_DisjointPathFamily G A B ι where
  a := F.a
  b := F.b
  p := fun i => (F.p i).mapLe hGG'
  ha := F.ha
  hb := F.hb
  hp := fun i => (Walk.mapLe_isPath hGG').2 (F.hp i)
  hdisj := by
    intro i j hij x hx hx'
    rw [Walk.support_mapLe_eq_support] at hx hx'
    exact F.hdisj hij hx hx'



omit [DecidableEq V] in


theorem bc17_exists_finInj_of_le_ncard {s : Set V} (hs : s.Finite) {k : ℕ}
    (hk : k ≤ s.ncard) :
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, f i ∈ s := by
  classical
  rw [Set.ncard_eq_toFinset_card s hs] at hk
  obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq hk
  refine ⟨fun i => (u.equivFin.symm (Fin.cast hcard.symm i) : V), ?_, ?_⟩
  · intro i j h
    have : u.equivFin.symm (Fin.cast hcard.symm i) = u.equivFin.symm (Fin.cast hcard.symm j) :=
      Subtype.ext h
    simpa [Fin.ext_iff] using (u.equivFin.symm.injective this)
  · intro i
    have hmem : (u.equivFin.symm (Fin.cast hcard.symm i) : V) ∈ u :=
      (u.equivFin.symm _).2
    exact hs.mem_toFinset.mp (hu hmem)





omit [DecidableEq V] in

theorem bc17_inter_isSeparator_bot (A B : Set V) :
    bc16_IsSeparator (⊥ : SimpleGraph V) A B (A ∩ B) := by
  intro s hs t ht p
  have hst : s = t := reachable_bot.mp p.reachable
  subst hst
  exact ⟨s, ⟨hs, ht⟩, p.start_mem_support⟩



def bc17_botFamily {A B : Set V} {k : ℕ} {f : Fin k → V} (hinj : Function.Injective f)
    (hf : ∀ i, f i ∈ A ∩ B) : bc16_DisjointPathFamily (⊥ : SimpleGraph V) A B (Fin k) where
  a := f
  b := f
  p := fun _ => Walk.nil
  ha := fun i => (hf i).1
  hb := fun i => (hf i).2
  hp := fun _ => Walk.IsPath.nil
  hdisj := by
    intro i j hij x hx hx'
    rw [Walk.support_nil, List.mem_singleton] at hx hx'
    exact hij (hinj (hx.symm.trans hx'))

omit [DecidableEq V] in



theorem bc17_hard_bot [Fintype V] (A B : Set V) {k : ℕ}
    (hsep : ∀ C, bc16_IsSeparator (⊥ : SimpleGraph V) A B C → k ≤ C.ncard) :
    Nonempty (bc16_DisjointPathFamily (⊥ : SimpleGraph V) A B (Fin k)) := by
  have hk : k ≤ (A ∩ B).ncard := hsep _ (bc17_inter_isSeparator_bot A B)
  obtain ⟨f, hinj, hf⟩ := bc17_exists_finInj_of_le_ncard (Set.toFinite (A ∩ B)) hk
  exact ⟨bc17_botFamily hinj hf⟩







variable {G : SimpleGraph V}

omit [DecidableEq V] in

theorem bc17_edgeSet_ncard_lt_of_deleteEdge [Fintype V] {x y : V} (h : G.Adj x y) :
    (G.deleteEdges {s(x, y)}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  refine Set.ncard_lt_ncard ⟨Set.diff_subset, ?_⟩ (Set.toFinite _)
  intro hsub
  have hmem : s(x, y) ∈ G.edgeSet := by simpa using h
  simpa using hsub hmem






theorem bc17_insert_isSeparator_left {A B Y : Set V} {x y : V}
    (hY : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y) :
    bc16_IsSeparator G A B (insert x Y) := by
  intro s hs t ht p
  by_cases he : s(x, y) ∈ p.edges
  · exact ⟨x, Set.mem_insert _ _, p.fst_mem_support_of_mem_edges he⟩
  · obtain ⟨c, hcY, hcp⟩ := hY hs ht (p.toDeleteEdge (s(x, y)) he)
    exact ⟨c, Set.mem_insert_of_mem _ hcY, by rwa [Walk.support_transfer] at hcp⟩



theorem bc17_insert_isSeparator_right {A B Y : Set V} {x y : V}
    (hY : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y) :
    bc16_IsSeparator G A B (insert y Y) := by
  intro s hs t ht p
  by_cases he : s(x, y) ∈ p.edges
  · refine ⟨y, Set.mem_insert _ _, ?_⟩
    exact p.snd_mem_support_of_mem_edges he
  · obtain ⟨c, hcY, hcp⟩ := hY hs ht (p.toDeleteEdge (s(x, y)) he)
    exact ⟨c, Set.mem_insert_of_mem _ hcY, by rwa [Walk.support_transfer] at hcp⟩




theorem bc17_endpoints_notMem_of_not_isSeparator {A B Y : Set V} {x y : V}
    (hY : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y)
    (hnotG : ¬ bc16_IsSeparator G A B Y) : x ∉ Y ∧ y ∉ Y := by
  refine ⟨fun hx => hnotG ?_, fun hy => hnotG ?_⟩
  · rw [← Set.insert_eq_self.mpr hx]; exact bc17_insert_isSeparator_left hY
  · rw [← Set.insert_eq_self.mpr hy]; exact bc17_insert_isSeparator_right hY





















theorem bc17_deleteEdge_dichotomy [Fintype V] {A B : Set V} {x y : V}
    (hxy : G.Adj x y) {k : ℕ}
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard) :
    (∀ C, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B C → k ≤ C.ncard) ∨
    (∃ Y : Set V, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y ∧ Y.ncard < k ∧
      x ∉ Y ∧ y ∉ Y ∧ bc16_IsSeparator G A B (insert x Y) ∧
      bc16_IsSeparator G A B (insert y Y)) := by
  classical
  by_cases hcase : ∀ C, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B C → k ≤ C.ncard
  · exact Or.inl hcase
  · refine Or.inr ?_
    push Not at hcase
    obtain ⟨Y, hY, hYlt⟩ := hcase
    
    have hnotG : ¬ bc16_IsSeparator G A B Y := fun hG => absurd (hmin Y hG) (by omega)
    obtain ⟨hx, hy⟩ := bc17_endpoints_notMem_of_not_isSeparator hY hnotG
    exact ⟨Y, hY, hYlt, hx, hy, bc17_insert_isSeparator_left hY,
      bc17_insert_isSeparator_right hY⟩







omit [DecidableEq V] in

theorem bc17_hard_zero (G : SimpleGraph V) (A B : Set V) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin 0)) :=
  ⟨{ a := fun i => i.elim0, b := fun i => i.elim0, p := fun i => i.elim0,
     ha := fun i => i.elim0, hb := fun i => i.elim0, hp := fun i => i.elim0,
     hdisj := fun i => i.elim0 }⟩

omit [DecidableEq V] in



theorem bc17_hard_one (G : SimpleGraph V) (A B : Set V)
    (hmin : ∀ C, bc16_IsSeparator G A B C → 1 ≤ C.ncard) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin 1)) := by
  
  have hne : ¬ bc16_IsSeparator G A B (∅ : Set V) := by
    intro h
    have := hmin _ h
    simp at this
  obtain ⟨s, hs, t, ht, p, hp⟩ := bc16_exists_path_of_not_empty_separator hne
  exact ⟨{ a := fun _ => s, b := fun _ => t, p := fun _ => p,
           ha := fun _ => hs, hb := fun _ => ht, hp := fun _ => hp,
           hdisj := fun i j hij => absurd (Subsingleton.elim i j) hij }⟩












def bc17_HardDir (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∀ k : ℕ, (∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard) →
    Nonempty (bc16_DisjointPathFamily G A B (Fin k))


theorem bc17_hardDir_bot [Fintype V] (A B : Set V) :
    bc17_HardDir (⊥ : SimpleGraph V) A B :=
  fun _ hmin => bc17_hard_bot A B hmin




theorem bc17_hardDir_step_case1 {G : SimpleGraph V} {A B : Set V} {x y : V} {k : ℕ}
    (hH : bc17_HardDir (G.deleteEdges {s(x, y)}) A B)
    (hC1 : ∀ C, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B C → k ≤ C.ncard) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin k)) := by
  obtain ⟨F⟩ := hH k hC1
  exact ⟨bc17_familyMapLe (deleteEdges_le _) F⟩












def bc17_restr (G : SimpleGraph V) (W : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ W ∧ v ∈ W
  symm := by rintro u v ⟨h, hu, hv⟩; exact ⟨h.symm, hv, hu⟩
  loopless := ⟨fun u ⟨h, _, _⟩ => G.loopless.irrefl u h⟩

@[simp] theorem bc17_restr_adj (G : SimpleGraph V) (W : Set V) {u v : V} :
    (bc17_restr G W).Adj u v ↔ G.Adj u v ∧ u ∈ W ∧ v ∈ W := Iff.rfl

omit [DecidableEq V] in

theorem bc17_restr_le (G : SimpleGraph V) (W : Set V) : bc17_restr G W ≤ G :=
  fun _ _ h => h.1

omit [DecidableEq V] in

theorem bc17_restr_support_subset (G : SimpleGraph V) (W : Set V) {a b : V} (ha : a ∈ W)
    (p : (bc17_restr G W).Walk a b) : ∀ z ∈ p.support, z ∈ W := by
  induction p with
  | nil => intro z hz; rw [Walk.support_nil, List.mem_singleton] at hz; exact hz ▸ ha
  | @cons u v w h q ih =>
      intro z hz
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ha
      · exact ih h.2.2 z hz

omit [DecidableEq V] in

theorem bc17_restr_edgeSet_subset (G : SimpleGraph V) (W : Set V) :
    (bc17_restr G W).edgeSet ⊆ G.edgeSet := edgeSet_mono (bc17_restr_le G W)




theorem bc17_restr_edgeSet_ncard_lt [Fintype V] (G : SimpleGraph V) (W : Set V) {x y : V}
    (hxy : G.Adj x y) (hy : y ∉ W) :
    (bc17_restr G W).edgeSet.ncard < G.edgeSet.ncard := by
  refine Set.ncard_lt_ncard ⟨bc17_restr_edgeSet_subset G W, ?_⟩ (Set.toFinite _)
  intro hsub
  have hmem : s(x, y) ∈ G.edgeSet := by simpa using hxy
  have := hsub hmem
  rw [mem_edgeSet, bc17_restr_adj] at this
  exact hy this.2.2







omit [DecidableEq V] in




theorem bc17_minmax_one [Fintype V] (G : SimpleGraph V) (A B : Set V)
    (hmin : ∀ C, bc16_IsSeparator G A B C → 1 ≤ C.ncard) :
    ∃ F : bc16_DisjointPathFamily G A B (Fin 1),
      ∀ C, bc16_IsSeparator G A B C → Fintype.card (Fin 1) ≤ C.ncard := by
  obtain ⟨F⟩ := bc17_hard_one G A B hmin
  exact ⟨F, fun C hC => by simpa using hmin C hC⟩




theorem bc17_minmax_bot [Fintype V] (A B : Set V) {k : ℕ}
    (hmin : ∀ C, bc16_IsSeparator (⊥ : SimpleGraph V) A B C → k ≤ C.ncard) :
    ∃ F : bc16_DisjointPathFamily (⊥ : SimpleGraph V) A B (Fin k),
      ∀ C, bc16_IsSeparator (⊥ : SimpleGraph V) A B C → Fintype.card (Fin k) ≤ C.ncard := by
  obtain ⟨F⟩ := bc17_hard_bot A B hmin
  exact ⟨F, fun C hC => by simpa using hmin C hC⟩

end StatMech.Walls
