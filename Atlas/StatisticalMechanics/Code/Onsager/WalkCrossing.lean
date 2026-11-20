/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































import Mathlib
import Code.Onsager.BaseCase
import Code.Onsager.NoDoubleWind

namespace StatMech.Onsager.WalkCrossing

open Finset
open StatMech.Onsager.BaseCase
open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]




def isVertEdge (w : Fin 4) : Prop := w = 1 ∨ w = 3


def isHorizEdge (w : Fin 4) : Prop := w = 0 ∨ w = 2

instance decVert (w : Fin 4) : Decidable (isVertEdge w) := by unfold isVertEdge; infer_instance
instance decHoriz (w : Fin 4) : Decidable (isHorizEdge w) := by unfold isHorizEdge; infer_instance


theorem snd_step (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).2 = (pos d k).2 + (stepOf (d k)).2 := by
  rw [pos_succ d hclosed k, Prod.snd_add]


theorem fst_step (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).1 = (pos d k).1 + (stepOf (d k)).1 := by
  rw [pos_succ d hclosed k, Prod.fst_add]


theorem vert_x_const (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isVertEdge (d k)) :
    (pos d (k + 1)).1 = (pos d k).1 := by
  rw [fst_step d hclosed k]
  rcases hk with h | h <;> rw [h] <;> simp [stepOf]


theorem vert_y_step (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isVertEdge (d k)) :
    (pos d (k + 1)).2 = (pos d k).2 + 1 ∨ (pos d (k + 1)).2 = (pos d k).2 - 1 := by
  rw [snd_step d hclosed k]
  rcases hk with h | h <;> rw [h]
  · left; simp [stepOf]
  · right; change (pos d k).2 + (-1 : ℤ) = (pos d k).2 - 1; ring


theorem horiz_y_const (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isHorizEdge (d k)) :
    (pos d (k + 1)).2 = (pos d k).2 := by
  rw [snd_step d hclosed k]
  rcases hk with h | h <;> rw [h] <;> simp [stepOf]


theorem horiz_x_step (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isHorizEdge (d k)) :
    (pos d (k + 1)).1 = (pos d k).1 + 1 ∨ (pos d (k + 1)).1 = (pos d k).1 - 1 := by
  rw [fst_step d hclosed k]
  rcases hk with h | h <;> rw [h]
  · left; simp [stepOf]
  · right; change (pos d k).1 + (-1 : ℤ) = (pos d k).1 - 1; ring


theorem stepOf_snd (w : Fin 4) : (stepOf w).2 = 0 ∨ (stepOf w).2 = 1 ∨ (stepOf w).2 = -1 := by
  fin_cases w <;> simp [stepOf]


theorem stepOf_fst (w : Fin 4) : (stepOf w).1 = 0 ∨ (stepOf w).1 = 1 ∨ (stepOf w).1 = -1 := by
  fin_cases w <;> simp [stepOf]


theorem snd_step_bound (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).2 = (pos d k).2 ∨ (pos d (k + 1)).2 = (pos d k).2 + 1 ∨
      (pos d (k + 1)).2 = (pos d k).2 - 1 := by
  have h := stepOf_snd (d k)
  rw [snd_step d hclosed k]; omega










def fullLineCross (d : Fin n → Fin 4) (m : ℤ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n =>
    isVertEdge (d k) ∧ min ((pos d k).2) ((pos d (k + 1)).2) = m)).card





theorem upDown_card_eq (d : Fin n → Fin 4) (_hclosed : ∑ i, stepOf (d i) = 0) (m : ℤ) :
    (Finset.univ.filter
        (fun k : Fin n => (pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2)).card
      = (Finset.univ.filter
        (fun k : Fin n => m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m)).card := by
  classical
  set g : Fin n → ℤ := fun k => if m + 1 ≤ (pos d k).2 then (1 : ℤ) else 0 with hg
  
  have hshift : (∑ k : Fin n, g (k + 1)) = ∑ k, g k :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n)) g
  have htel : (∑ k : Fin n, (g (k + 1) - g k)) = 0 := by
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  
  have hper : ∀ k : Fin n, g (k + 1) - g k
      = (if ((pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2) then (1 : ℤ) else 0)
        - (if (m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m) then (1 : ℤ) else 0) := by
    intro k
    simp only [hg]
    split_ifs <;> omega
  
  have hsum : (∑ k : Fin n,
        ((if ((pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2) then (1 : ℤ) else 0)
          - (if (m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m) then (1 : ℤ) else 0))) = 0 := by
    have hcong : (∑ k : Fin n,
        ((if ((pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2) then (1 : ℤ) else 0)
          - (if (m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m) then (1 : ℤ) else 0)))
        = ∑ k : Fin n, (g (k + 1) - g k) :=
      Finset.sum_congr rfl (fun k _ => (hper k).symm)
    rw [hcong]; exact htel
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, sub_eq_zero] at hsum
  exact_mod_cast hsum




theorem fullLineCross_even (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (m : ℤ) :
    Even (fullLineCross d m) := by
  classical
  
  set Pup : Fin n → Prop := fun k => (pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2 with hPup
  set Pdown : Fin n → Prop := fun k => m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m with hPdown
  have hiff : ∀ k : Fin n,
      (isVertEdge (d k) ∧ min ((pos d k).2) ((pos d (k + 1)).2) = m) ↔ (Pup k ∨ Pdown k) := by
    intro k
    simp only [hPup, hPdown]
    constructor
    · rintro ⟨hv, hmin⟩
      rcases vert_y_step d hclosed k hv with h | h <;> rw [h] at hmin ⊢ <;> omega
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · 
        rcases snd_step_bound d hclosed k with h | h | h
        · omega
        · refine ⟨?_, by rw [h]; omega⟩
          
          rcases show isVertEdge (d k) ∨ isHorizEdge (d k) from by
            rcases stepOf_coords (d k) with ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩
            · exact Or.inr (Or.inl hd)
            · exact Or.inl (Or.inl hd)
            · exact Or.inr (Or.inr hd)
            · exact Or.inl (Or.inr hd) with hvv | hhh
          · exact hvv
          · exact absurd (horiz_y_const d hclosed k hhh) (by omega)
        · omega
      · rcases snd_step_bound d hclosed k with h | h | h
        · omega
        · omega
        · refine ⟨?_, by rw [h]; omega⟩
          rcases show isVertEdge (d k) ∨ isHorizEdge (d k) from by
            rcases stepOf_coords (d k) with ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩
            · exact Or.inr (Or.inl hd)
            · exact Or.inl (Or.inl hd)
            · exact Or.inr (Or.inr hd)
            · exact Or.inl (Or.inr hd) with hvv | hhh
          · exact hvv
          · exact absurd (horiz_y_const d hclosed k hhh) (by omega)
  have hdisj : Disjoint (Finset.univ.filter Pup) (Finset.univ.filter Pdown) := by
    rw [Finset.disjoint_filter]
    intro k _ hup hdown
    simp only [hPup] at hup; simp only [hPdown] at hdown; omega
  have hsplit : (Finset.univ.filter (fun k : Fin n =>
        isVertEdge (d k) ∧ min ((pos d k).2) ((pos d (k + 1)).2) = m))
      = (Finset.univ.filter Pup) ∪ (Finset.univ.filter Pdown) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact hiff k
  have heq : (Finset.univ.filter Pup).card = (Finset.univ.filter Pdown).card := by
    simp only [hPup, hPdown]; exact upDown_card_eq d hclosed m
  rw [fullLineCross, hsplit, Finset.card_union_of_disjoint hdisj, heq]
  exact ⟨_, rfl⟩











def onEdge (d : Fin n → Fin 4) (k : Fin n) (p : ℤ × ℤ) : Prop :=
  (min (pos d k).1 (pos d (k + 1)).1 ≤ p.1 ∧ p.1 ≤ max (pos d k).1 (pos d (k + 1)).1) ∧
    (min (pos d k).2 (pos d (k + 1)).2 ≤ p.2 ∧ p.2 ≤ max (pos d k).2 (pos d (k + 1)).2)



theorem onEdge_horiz_endpoint (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isHorizEdge (d k)) (p : ℤ × ℤ) (hp : onEdge d k p) :
    p = pos d k ∨ p = pos d (k + 1) := by
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hp
  have hyc := horiz_y_const d hclosed k hk
  have hxs := horiz_x_step d hclosed k hk
  have hpy : p.2 = (pos d k).2 := by omega
  have hpx : p.1 = (pos d k).1 ∨ p.1 = (pos d (k + 1)).1 := by
    rcases hxs with h | h <;> rw [h] at hx1 hx2 ⊢ <;> omega
  rcases hpx with h | h
  · exact Or.inl (Prod.ext h hpy)
  · exact Or.inr (Prod.ext h (by rw [hpy]; exact hyc.symm))


theorem onEdge_vert_endpoint (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isVertEdge (d k)) (p : ℤ × ℤ) (hp : onEdge d k p) :
    p = pos d k ∨ p = pos d (k + 1) := by
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hp
  have hxc := vert_x_const d hclosed k hk
  have hys := vert_y_step d hclosed k hk
  have hpx : p.1 = (pos d k).1 := by omega
  have hpy : p.2 = (pos d k).2 ∨ p.2 = (pos d (k + 1)).2 := by
    rcases hys with h | h <;> rw [h] at hy1 hy2 ⊢ <;> omega
  rcases hpy with h | h
  · exact Or.inl (Prod.ext hpx h)
  · exact Or.inr (Prod.ext (by rw [hpx]; exact hxc.symm) h)




theorem horiz_vert_cross_shared_vertex (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k j : Fin n) (hk : isHorizEdge (d k)) (hj : isVertEdge (d j)) (p : ℤ × ℤ)
    (hpk : onEdge d k p) (hpj : onEdge d j p) :
    (p = pos d k ∨ p = pos d (k + 1)) ∧ (p = pos d j ∨ p = pos d (j + 1)) :=
  ⟨onEdge_horiz_endpoint d hclosed k hk p hpk, onEdge_vert_endpoint d hclosed j hj p hpj⟩






theorem edges_cross_not_injective (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k j : Fin n) (hk : isHorizEdge (d k)) (hj : isVertEdge (d j))
    (hne1 : k ≠ j) (hne2 : k + 1 ≠ j) (hne3 : k ≠ j + 1) (hne4 : k + 1 ≠ j + 1)
    (p : ℤ × ℤ) (hpk : onEdge d k p) (hpj : onEdge d j p) :
    ¬ Function.Injective (pos d) := by
  intro hinj
  rcases onEdge_horiz_endpoint d hclosed k hk p hpk with hak | hak <;>
    rcases onEdge_vert_endpoint d hclosed j hj p hpj with hbj | hbj
  · exact hne1 (hinj (hak.symm.trans hbj))
  · exact hne3 (hinj (hak.symm.trans hbj))
  · exact hne2 (hinj (hak.symm.trans hbj))
  · exact hne4 (hinj (hak.symm.trans hbj))








def rayCross (d : Fin n → Fin 4) (m qx : ℤ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n =>
    isVertEdge (d k) ∧ qx < (pos d k).1 ∧
      min ((pos d k).2) ((pos d (k + 1)).2) = m)).card


theorem rayCross_le_fullLineCross (d : Fin n → Fin 4) (m qx : ℤ) :
    rayCross d m qx ≤ fullLineCross d m := by
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.1, hk.2.2.2⟩

end StatMech.Onsager.WalkCrossing
