/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.CrossingParity
import Code.Lattice.WindingWitness
import Code.Walls.wndwinding
import Code.Walls.wnuupperhalf
import Code.Walls.wnaalternate

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice




def wcb_column (p : Site 2) : ℤ := p 0




def wcb_canonRayEdge (z : Site 2) (c : ℤ) : Sym2 (Site 2) :=
  s(![c, z 1 - 1], ![c, z 1])


theorem wcb_rayEdge_column (z x y : Site 2) (h : jec_rayEdge z s(x, y)) :
    x 0 = y 0 := by
  rw [jec_rayEdge_mk] at h
  exact h.1.1




theorem wcb_rayEdge_eq_of_column (z x y : Site 2) (h : jec_rayEdge z s(x, y)) :
    s(x, y) = wcb_canonRayEdge z (x 0) := by
  rw [jec_rayEdge_mk] at h
  obtain ⟨⟨hxy, _hle⟩, hcase⟩ := h
  unfold wcb_canonRayEdge
  rcases hcase with ⟨hx1, hy1⟩ | ⟨hy1, hx1⟩
  · 
    have hx : x = ![x 0, z 1 - 1] := by
      ext i; fin_cases i <;> simp [hx1]
    have hy : y = ![x 0, z 1] := by
      ext i; fin_cases i <;> simp [hxy.symm, hy1]
    rw [hx, hy]; norm_num
  · 
    have hx : x = ![x 0, z 1] := by
      ext i; fin_cases i <;> simp [hx1]
    have hy : y = ![x 0, z 1 - 1] := by
      ext i; fin_cases i <;> simp [hxy.symm, hy1]
    rw [hx, hy, Sym2.eq_swap]; norm_num




theorem wcb_rayEdge_injOn_column (z x₁ y₁ x₂ y₂ : Site 2)
    (h₁ : jec_rayEdge z s(x₁, y₁)) (h₂ : jec_rayEdge z s(x₂, y₂))
    (hcol : x₁ 0 = x₂ 0) :
    s(x₁, y₁) = s(x₂, y₂) := by
  rw [wcb_rayEdge_eq_of_column z x₁ y₁ h₁, wcb_rayEdge_eq_of_column z x₂ y₂ h₂, hcol]





def wcb_dartColumn (d : (hypercubicLattice 2).Dart) : ℤ := d.toProd.1 0


theorem wcb_dartColumn_eq_head (z : Site 2) (d : (hypercubicLattice 2).Dart)
    (h : jec_rayEdge z s(d.toProd.1, d.toProd.2)) :
    wcb_dartColumn d = d.toProd.2 0 :=
  wcb_rayEdge_column z d.toProd.1 d.toProd.2 h


theorem wcb_dart_edge (d : (hypercubicLattice 2).Dart) :
    d.edge = s(d.toProd.1, d.toProd.2) := SimpleGraph.Dart.edge_mk ..





theorem wcb_crossing_edges_distinct_columns (z : Site 2)
    (d₁ d₂ : (hypercubicLattice 2).Dart)
    (h₁ : jec_rayEdge z d₁.edge) (h₂ : jec_rayEdge z d₂.edge)
    (hcol : wcb_dartColumn d₁ = wcb_dartColumn d₂) :
    d₁.edge = d₂.edge := by
  rw [wcb_dart_edge] at h₁ h₂ ⊢
  exact wcb_rayEdge_injOn_column z d₁.toProd.1 d₁.toProd.2 d₂.toProd.1 d₂.toProd.2 h₁ h₂ hcol







noncomputable def wcb_keyedList (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : List (ℤ × ℤ) :=
  (w.darts.map (fun d => (wcb_dartColumn d, wnd_signStep z d.toProd.1 d.toProd.2))).filter
    (fun p => p.2 ≠ 0)



private theorem wcb_map_snd_filter (L : List ((hypercubicLattice 2).Dart))
    (g : (hypercubicLattice 2).Dart → ℤ) (k : (hypercubicLattice 2).Dart → ℤ) :
    ((L.map (fun d => (k d, g d))).filter (fun p => p.2 ≠ 0)).map Prod.snd =
      (L.map g).filter (fun s => s ≠ 0) := by
  classical
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons]
    by_cases ha : g a = 0
    · rw [List.filter_cons_of_neg (by simp [ha]), List.filter_cons_of_neg (by simp [ha]), ih]
    · rw [List.filter_cons_of_pos (by simp [ha]), List.filter_cons_of_pos (by simp [ha]),
        List.map_cons, ih]


theorem wcb_keyedList_snd (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    (wcb_keyedList z w).map Prod.snd = wnu_signedList z w := by
  classical
  unfold wcb_keyedList wnu_signedList
  exact wcb_map_snd_filter w.darts
    (fun d => wnd_signStep z d.toProd.1 d.toProd.2) (fun d => wcb_dartColumn d)




noncomputable def wcb_columnSorted (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : List ℤ :=
  ((wcb_keyedList z w).insertionSort (fun p q => p.1 ≤ q.1)).map Prod.snd







theorem wcb_columnOrder_permutes_signedList (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    (wcb_columnSorted z w).Perm (wnu_signedList z w) := by
  classical
  unfold wcb_columnSorted
  
  have hperm : ((wcb_keyedList z w).insertionSort (fun p q => p.1 ≤ q.1)).Perm
      (wcb_keyedList z w) := List.perm_insertionSort _ _
  have h1 : (((wcb_keyedList z w).insertionSort (fun p q => p.1 ≤ q.1)).map Prod.snd).Perm
      ((wcb_keyedList z w).map Prod.snd) := hperm.map _
  rw [wcb_keyedList_snd z w] at h1
  exact h1



theorem wcb_columnSorted_sum (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    (wcb_columnSorted z w).sum = wnd_signedCross z w := by
  rw [(wcb_columnOrder_permutes_signedList z w).sum_eq, wnu_signedList_sum]



theorem wcb_columnSorted_entries_pm (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    ∀ s ∈ wcb_columnSorted z w, s = 1 ∨ s = -1 := by
  classical
  intro s hs
  
  have hmem : s ∈ wnu_signedList z w :=
    (wcb_columnOrder_permutes_signedList z w).mem_iff.mp hs
  unfold wnu_signedList at hmem
  rw [List.mem_filter] at hmem
  obtain ⟨hmap, hne⟩ := hmem
  rw [List.mem_map] at hmap
  obtain ⟨d, _, hd⟩ := hmap
  
  have hmem3 := wnd_signStep_mem z d.toProd.1 d.toProd.2
  rw [hd] at hmem3
  have hne' : s ≠ 0 := by simpa using hne
  rcases hmem3 with h | h | h
  · exact Or.inl h
  · exact absurd h hne'
  · exact Or.inr h
















theorem wcb_columnAlternates_of_sorted_alt (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (halt : wnu_Alt (wcb_columnSorted z w)) :
    wna_ColumnAlternates z w :=
  ⟨wcb_columnSorted z w, wcb_columnOrder_permutes_signedList z w, halt⟩








theorem wcb_unitSquare_columnSorted :
    wcb_columnSorted (![1, 1] : Site 2) wwit_unitSquareLoop = [1] := by
  have hperm := wcb_columnOrder_permutes_signedList (![1, 1] : Site 2) wwit_unitSquareLoop
  rw [wnu_unitSquare_signedList] at hperm
  
  exact hperm.eq_singleton



theorem wcb_unitSquare_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop := by
  apply wcb_columnAlternates_of_sorted_alt
  rw [wcb_unitSquare_columnSorted]
  exact Or.inl rfl



theorem wcb_Ltromino_columnSorted :
    wcb_columnSorted (![1, 1] : Site 2) wnu_LtrominoLoop = [-1] := by
  have hperm := wcb_columnOrder_permutes_signedList (![1, 1] : Site 2) wnu_LtrominoLoop
  rw [wnu_Ltromino_signedList] at hperm
  exact hperm.eq_singleton


theorem wcb_Ltromino_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop := by
  apply wcb_columnAlternates_of_sorted_alt
  rw [wcb_Ltromino_columnSorted]
  exact Or.inr rfl














theorem wcb_doubleSquare_columnSorted :
    wcb_columnSorted (![1, 1] : Site 2) wnu_doubleSquare = [1, 1] := by
  have hperm := wcb_columnOrder_permutes_signedList (![1, 1] : Site 2) wnu_doubleSquare
  rw [wnu_doubleSquare_signedList] at hperm
  
  have hlen := hperm.length_eq
  have hmem : ∀ s ∈ wcb_columnSorted (![1, 1] : Site 2) wnu_doubleSquare, s = 1 := by
    intro s hs
    have := hperm.mem_iff.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h <;> exact h
  match wcb_columnSorted (![1, 1] : Site 2) wnu_doubleSquare, hlen, hmem with
  | [a, b], _, hmem =>
    have ha := hmem a (by simp)
    have hb := hmem b (by simp)
    rw [ha, hb]




theorem wcb_doubleSquare_not_columnSorted_alt :
    ¬ wnu_Alt (wcb_columnSorted (![1, 1] : Site 2) wnu_doubleSquare) := by
  rw [wcb_doubleSquare_columnSorted]
  exact wnu_not_alt_oneOne







































end Lattice

end StatMech
