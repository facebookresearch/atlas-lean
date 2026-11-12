/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.WalkCrossing









namespace StatMech.Onsager.WalkCrossingV

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing

variable {n : ℕ} [NeZero n]


theorem fst_step_bound (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).1 = (pos d k).1 ∨ (pos d (k + 1)).1 = (pos d k).1 + 1 ∨
      (pos d (k + 1)).1 = (pos d k).1 - 1 := by
  have h := stepOf_fst (d k)
  rw [fst_step d hclosed k]; omega



def vertColCross (d : Fin n → Fin 4) (m : ℤ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n =>
    isHorizEdge (d k) ∧ min ((pos d k).1) ((pos d (k + 1)).1) = m)).card


theorem leftRight_card_eq (d : Fin n → Fin 4) (m : ℤ) :
    (Finset.univ.filter
        (fun k : Fin n => (pos d k).1 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).1)).card
      = (Finset.univ.filter
        (fun k : Fin n => m + 1 ≤ (pos d k).1 ∧ (pos d (k + 1)).1 ≤ m)).card := by
  classical
  set g : Fin n → ℤ := fun k => if m + 1 ≤ (pos d k).1 then (1 : ℤ) else 0 with hg
  have hshift : (∑ k : Fin n, g (k + 1)) = ∑ k, g k :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n)) g
  have htel : (∑ k : Fin n, (g (k + 1) - g k)) = 0 := by
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  have hper : ∀ k : Fin n, g (k + 1) - g k
      = (if ((pos d k).1 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).1) then (1 : ℤ) else 0)
        - (if (m + 1 ≤ (pos d k).1 ∧ (pos d (k + 1)).1 ≤ m) then (1 : ℤ) else 0) := by
    intro k
    simp only [hg]
    split_ifs <;> omega
  have hsum : (∑ k : Fin n,
        ((if ((pos d k).1 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).1) then (1 : ℤ) else 0)
          - (if (m + 1 ≤ (pos d k).1 ∧ (pos d (k + 1)).1 ≤ m) then (1 : ℤ) else 0))) = 0 := by
    have hcong : (∑ k : Fin n,
        ((if ((pos d k).1 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).1) then (1 : ℤ) else 0)
          - (if (m + 1 ≤ (pos d k).1 ∧ (pos d (k + 1)).1 ≤ m) then (1 : ℤ) else 0)))
        = ∑ k : Fin n, (g (k + 1) - g k) :=
      Finset.sum_congr rfl (fun k _ => (hper k).symm)
    rw [hcong]; exact htel
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, sub_eq_zero] at hsum
  exact_mod_cast hsum



theorem vertColCross_even (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (m : ℤ) :
    Even (vertColCross d m) := by
  classical
  set Pl : Fin n → Prop := fun k => (pos d k).1 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).1 with hPl
  set Pr : Fin n → Prop := fun k => m + 1 ≤ (pos d k).1 ∧ (pos d (k + 1)).1 ≤ m with hPr
  have hiff : ∀ k : Fin n,
      (isHorizEdge (d k) ∧ min ((pos d k).1) ((pos d (k + 1)).1) = m) ↔ (Pl k ∨ Pr k) := by
    intro k
    simp only [hPl, hPr]
    constructor
    · rintro ⟨hh, hmin⟩
      rcases horiz_x_step d hclosed k hh with h | h <;> rw [h] at hmin ⊢ <;> omega
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · rcases fst_step_bound d hclosed k with h | h | h
        · omega
        · refine ⟨?_, by rw [h]; omega⟩
          rcases show isVertEdge (d k) ∨ isHorizEdge (d k) from by
            rcases stepOf_coords (d k) with ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩
            · exact Or.inr (Or.inl hd)
            · exact Or.inl (Or.inl hd)
            · exact Or.inr (Or.inr hd)
            · exact Or.inl (Or.inr hd) with hvv | hhh
          · exact absurd (vert_x_const d hclosed k hvv) (by omega)
          · exact hhh
        · omega
      · rcases fst_step_bound d hclosed k with h | h | h
        · omega
        · omega
        · refine ⟨?_, by rw [h]; omega⟩
          rcases show isVertEdge (d k) ∨ isHorizEdge (d k) from by
            rcases stepOf_coords (d k) with ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩
            · exact Or.inr (Or.inl hd)
            · exact Or.inl (Or.inl hd)
            · exact Or.inr (Or.inr hd)
            · exact Or.inl (Or.inr hd) with hvv | hhh
          · exact absurd (vert_x_const d hclosed k hvv) (by omega)
          · exact hhh
  have hdisj : Disjoint (Finset.univ.filter Pl) (Finset.univ.filter Pr) := by
    rw [Finset.disjoint_filter]
    intro k _ hl hr
    simp only [hPl] at hl; simp only [hPr] at hr; omega
  have hsplit : (Finset.univ.filter (fun k : Fin n =>
        isHorizEdge (d k) ∧ min ((pos d k).1) ((pos d (k + 1)).1) = m))
      = (Finset.univ.filter Pl) ∪ (Finset.univ.filter Pr) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact hiff k
  have heq : (Finset.univ.filter Pl).card = (Finset.univ.filter Pr).card := by
    simp only [hPl, hPr]; exact leftRight_card_eq d m
  rw [vertColCross, hsplit, Finset.card_union_of_disjoint hdisj, heq]
  exact ⟨_, rfl⟩

end StatMech.Onsager.WalkCrossingV
