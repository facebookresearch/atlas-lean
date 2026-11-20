/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.Sharpness.Switching

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech
namespace Sharpness
namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]





noncomputable def compOddVertices (ends : ι → Sym2 V) (m : Finset ι) (u : V) : Finset V :=
  (compOf ends m u).filter (fun x => Odd (degK ends m x))

@[simp] theorem mem_compOddVertices {ends : ι → Sym2 V} {m : Finset ι} {u x : V} :
    x ∈ compOddVertices ends m u ↔ connK ends m u x ∧ Odd (degK ends m x) := by
  simp [compOddVertices, mem_compOf]





theorem even_compOddVertices (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (u : V) :
    Even (compOddVertices ends m u).card := by
  have hsum := sum_deg_comp_even ends m hnd u
  rw [even_sum_iff_even_count] at hsum
  exact hsum


theorem compOddVertices_eq_filter_sources (ends : ι → Sym2 V) (m : Finset ι) (u : V) :
    compOddVertices ends m u = (sources ends m).filter (fun x => connK ends m u x) := by
  ext x
  simp only [mem_compOddVertices, Finset.mem_filter, mem_sources]
  tauto





theorem compOddVertices_mem_of_source (ends : ι → Sym2 V) (m : Finset ι)
    {o w : V} (hw : w ∈ sources ends m) (hconn : connK ends m o w) :
    w ∈ compOddVertices ends m o := by
  rw [compOddVertices_eq_filter_sources, Finset.mem_filter]
  exact ⟨hw, hconn⟩










theorem compOddVertices_o_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g})
    (hng : ¬ connK ends m o g) :
    compOddVertices ends m o = {o, x} ∨ compOddVertices ends m o = {o, y} := by
  classical
  set C := compOddVertices ends m o with hC
  
  have hCsub : C ⊆ ({o, x, y, g} : Finset V) := by
    intro w hw
    rw [hC, compOddVertices_eq_filter_sources, Finset.mem_filter, hsrc] at hw
    exact hw.1
  
  have hoC : o ∈ C := by
    rw [hC]
    refine compOddVertices_mem_of_source ends m ?_ Relation.ReflTransGen.refl
    rw [hsrc]; simp
  
  have hgC : g ∉ C := by
    rw [hC, compOddVertices_eq_filter_sources, Finset.mem_filter]
    rintro ⟨_, hcon⟩; exact hng hcon
  
  have hCeven : Even C.card := even_compOddVertices ends m hnd o
  
  
  have hCsub3 : C ⊆ ({o, x, y} : Finset V) := by
    intro w hw
    have hw4 := hCsub hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw4 ⊢
    rcases hw4 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd (h ▸ hw) hgC
  
  by_cases hxC : x ∈ C <;> by_cases hyC : y ∈ C
  · 
    exfalso
    have hCeq : C = ({o, x, y} : Finset V) := by
      apply Finset.Subset.antisymm hCsub3
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hoC
      · exact hxC
      · exact hyC
    have : C.card = 3 := by
      rw [hCeq, Finset.card_insert_of_notMem (by simp [hox, hoy]),
        Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    rw [this] at hCeven
    exact (by decide : ¬ Even 3) hCeven
  · 
    left
    apply Finset.Subset.antisymm
    · intro w hw
      have hw3 := hCsub3 hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw3 ⊢
      rcases hw3 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (h ▸ hw) hyC
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hoC
      · exact hxC
  · 
    right
    apply Finset.Subset.antisymm
    · intro w hw
      have hw3 := hCsub3 hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw3 ⊢
      rcases hw3 with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hw) hxC
      · exact Or.inr h
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hoC
      · exact hyC
  · 
    exfalso
    have hCeq : C = ({o} : Finset V) := by
      apply Finset.Subset.antisymm
      · intro w hw
        have hw3 := hCsub3 hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw3 ⊢
        rcases hw3 with h | h | h
        · exact h
        · exact absurd (h ▸ hw) hxC
        · exact absurd (h ▸ hw) hyC
      · intro w hw; rw [Finset.mem_singleton] at hw; rw [hw]; exact hoC
    rw [hCeq, Finset.card_singleton] at hCeven
    exact (by decide : ¬ Even 1) hCeven




theorem connK_of_compOddVertices_eq_pair (ends : ι → Sym2 V) (m : Finset ι)
    {o w z : V} (heq : compOddVertices ends m o = {o, w})
    (hzsrc : z ∈ sources ends m) (hzne_o : z ≠ o) (hzne_w : z ≠ w) :
    connK ends m o w ∧ ¬ connK ends m o z := by
  constructor
  · have : w ∈ compOddVertices ends m o := by rw [heq]; simp
    rw [mem_compOddVertices] at this; exact this.1
  · intro hcon
    have : z ∈ compOddVertices ends m o :=
      compOddVertices_mem_of_source ends m hzsrc hcon
    rw [heq] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact hzne_o h
    · exact hzne_w h


















theorem disconnect_dichotomy (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g})
    (hng : ¬ connK ends m o g) :
    (connK ends m o x ∧ connK ends m y g) ∨ (connK ends m o y ∧ connK ends m x g) := by
  classical
  
  have hxsrc : x ∈ sources ends m := by rw [hsrc]; simp
  have hysrc : y ∈ sources ends m := by rw [hsrc]; simp
  have hgsrc : g ∈ sources ends m := by rw [hsrc]; simp
  have hosrc : o ∈ sources ends m := by rw [hsrc]; simp
  
  have hsrc_g : sources ends m = {g, x, y, o} := by
    rw [hsrc]; ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  
  have hngo : ¬ connK ends m g o := fun h => hng (connK_symm ends m h)
  
  have hgdich : compOddVertices ends m g = {g, x} ∨ compOddVertices ends m g = {g, y} := by
    have := compOddVertices_o_eq ends m hnd
      (o := g) (x := x) (y := y) (g := o)
      hxg.symm hyg.symm hog.symm hxy hox.symm hoy.symm hsrc_g hngo
    
    exact this
  rcases compOddVertices_o_eq ends m hnd hox hoy hog hxy hxg hyg hsrc hng with hox' | hoy'
  · 
    left
    obtain ⟨hconnox, _hnoy⟩ :=
      connK_of_compOddVertices_eq_pair ends m hox' hysrc hoy.symm hxy.symm
    
    have hngx : ¬ connK ends m g x := by
      intro hgx
      exact hngo ((hgx.trans (connK_symm ends m hconnox)))
    
    have hgy : compOddVertices ends m g = {g, y} := by
      rcases hgdich with hgx | hgy
      · exfalso
        have : x ∈ compOddVertices ends m g := by rw [hgx]; simp
        rw [mem_compOddVertices] at this
        exact hngx this.1
      · exact hgy
    
    have : y ∈ compOddVertices ends m g := by rw [hgy]; simp
    rw [mem_compOddVertices] at this
    exact ⟨hconnox, connK_symm ends m this.1⟩
  · 
    right
    obtain ⟨hconnoy, _hnox⟩ :=
      connK_of_compOddVertices_eq_pair ends m hoy' hxsrc hox.symm hxy
    
    have hngy : ¬ connK ends m g y := by
      intro hgy
      exact hngo ((hgy.trans (connK_symm ends m hconnoy)))
    
    have hgx : compOddVertices ends m g = {g, x} := by
      rcases hgdich with hgx | hgy
      · exact hgx
      · exfalso
        have : y ∈ compOddVertices ends m g := by rw [hgy]; simp
        rw [mem_compOddVertices] at this
        exact hngy this.1
    
    have : x ∈ compOddVertices ends m g := by rw [hgx]; simp
    rw [mem_compOddVertices] at this
    exact ⟨hconnoy, connK_symm ends m this.1⟩









theorem disconnect_dichotomy_prop (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g})
    (hng : ¬ connK ends m o g) :
    (connK ends m o x ∧ connK ends m y g) ↔ ¬ (connK ends m o y ∧ connK ends m x g) := by
  have hdich := disconnect_dichotomy ends m hnd hox hoy hog hxy hxg hyg hsrc hng
  
  have hexcl : ¬ ((connK ends m o x ∧ connK ends m y g)
      ∧ (connK ends m o y ∧ connK ends m x g)) := by
    rintro ⟨⟨hox', _⟩, ⟨hoy', _⟩⟩
    
    rcases compOddVertices_o_eq ends m hnd hox hoy hog hxy hxg hyg hsrc hng with heq | heq
    · 
      have hyin : y ∈ compOddVertices ends m o :=
        compOddVertices_mem_of_source ends m (by rw [hsrc]; simp) hoy'
      rw [heq] at hyin
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyin
      rcases hyin with h | h
      · exact hoy h.symm
      · exact hxy h.symm
    · 
      have hxin : x ∈ compOddVertices ends m o :=
        compOddVertices_mem_of_source ends m (by rw [hsrc]; simp) hox'
      rw [heq] at hxin
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxin
      rcases hxin with h | h
      · exact hox h.symm
      · exact hxy h
  constructor
  · intro hA hB; exact hexcl ⟨hA, hB⟩
  · intro hnB; rcases hdich with hA | hB
    · exact hA
    · exact absurd hB hnB














theorem connK_yg_of_disconnected (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g})
    (hny : ¬ connK ends m o y) (hng : ¬ connK ends m o g) :
    connK ends m y g := by
  rcases disconnect_dichotomy ends m hnd hox hoy hog hxy hxg hyg hsrc hng with ⟨_, hyg'⟩ | ⟨hoy', _⟩
  · exact hyg'
  · exact absurd hoy' hny










def witEnds : Fin 2 → Sym2 (Fin 4)
  | 0 => s(0, 1)
  | 1 => s(2, 3)


def witM : Finset (Fin 2) := Finset.univ

theorem witEnds_not_diag : ∀ i ∈ witM, ¬ (witEnds i).IsDiag := by decide

theorem witM_sources : sources witEnds witM = {0, 1, 2, 3} := by decide

theorem witM_connK_ox : connK witEnds witM 0 1 :=
  Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩

theorem witM_connK_yg : connK witEnds witM 2 3 :=
  Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩




theorem witM_not_connK_og : ¬ connK witEnds witM 0 3 := by
  
  have hclosed : ∀ a b : Fin 4, adjStep witEnds witM a b → (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) := by
    rintro a b ⟨i, _, ha, hb, _⟩ hab
    fin_cases i
    · 
      simp only [witEnds, Sym2.mem_iff] at ha hb
      rcases hb with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
    · 
      exfalso
      simp only [witEnds, Sym2.mem_iff] at ha
      rcases hab with rfl | rfl <;> rcases ha with h | h <;> exact absurd h (by decide)
  intro h
  
  have hkey : ∀ b : Fin 4, connK witEnds witM 0 b → (b = 0 ∨ b = 1) := by
    intro b hb
    induction hb with
    | refl => exact Or.inl rfl
    | tail _ hstep ih => exact hclosed _ _ hstep ih
  rcases hkey 3 h with h' | h' <;> exact absurd h' (by decide)



theorem disconnect_dichotomy_nonvacuous :
    sources witEnds witM = ({(0 : Fin 4), 1, 2, 3} : Finset (Fin 4))
      ∧ ¬ connK witEnds witM 0 3
      ∧ ((connK witEnds witM 0 1 ∧ connK witEnds witM 2 3)
          ∨ (connK witEnds witM 0 2 ∧ connK witEnds witM 1 3)) :=
  ⟨witM_sources, witM_not_connK_og,
    disconnect_dichotomy witEnds witM witEnds_not_diag
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      witM_sources witM_not_connK_og⟩

end RandomCurrent
end Sharpness
end StatMech
