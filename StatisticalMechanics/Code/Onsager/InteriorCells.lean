/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.JordanParity
import Code.Onsager.WalkCrossingV











namespace StatMech.Onsager.InteriorCells

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.WalkCrossingV StatMech.Onsager.JordanParity

variable {n : ℕ} [NeZero n]


def interiorSet (d : Fin n → Fin 4) : Set (ℤ × ℤ) := {c | rayParity d c.1 c.2 = 1}


noncomputable def yInf (d : Fin n → Fin 4) : ℤ := Finset.univ.inf' Finset.univ_nonempty (fun k => (pos d k).2)


noncomputable def ySup (d : Fin n → Fin 4) : ℤ := Finset.univ.sup' Finset.univ_nonempty (fun k => (pos d k).2)

theorem yInf_le (d : Fin n → Fin 4) (k : Fin n) : yInf d ≤ (pos d k).2 :=
  Finset.inf'_le (fun k => (pos d k).2) (Finset.mem_univ k)

theorem le_ySup (d : Fin n → Fin 4) (k : Fin n) : (pos d k).2 ≤ ySup d :=
  Finset.le_sup' (fun k => (pos d k).2) (Finset.mem_univ k)


theorem exists_edge_of_rayParity (d : Fin n → Fin 4) (a b : ℤ) (h : rayParity d a b = 1) :
    ∃ k : Fin n, isHorizEdge (d k) ∧ min ((pos d k).1) ((pos d (k + 1)).1) = a ∧ b < (pos d k).2 := by
  by_contra hcon
  push_neg at hcon
  have hz : upCross d a b = 0 := by
    unfold upCross
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _
    rintro ⟨hh, hm, hb⟩
    exact absurd hb (by have := hcon k hh hm; omega)
  rw [rayParity, hz] at h
  simp at h



theorem rayParity_zero_of_lt_yInf (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (a b : ℤ) (hb : b < yInf d) : rayParity d a b = 0 := by
  have heq : upCross d a b = vertColCross d a := by
    unfold upCross vertColCross
    congr 1
    apply Finset.filter_congr
    intro k _
    constructor
    · rintro ⟨hh, hm, _⟩; exact ⟨hh, hm⟩
    · rintro ⟨hh, hm⟩; exact ⟨hh, hm, lt_of_lt_of_le hb (yInf_le d k)⟩
  rw [rayParity, heq]
  obtain ⟨t, ht⟩ := vertColCross_even d hclosed a
  rw [ht]
  push_cast
  rw [← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]


theorem interiorSet_finite (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) :
    (interiorSet d).Finite := by
  apply Set.Finite.subset
    (Set.Finite.prod
      (Finset.univ.image (fun k => min ((pos d k).1) ((pos d (k + 1)).1))).finite_toSet
      (Set.finite_Ico (yInf d) (ySup d)))
  intro c hc
  simp only [interiorSet, Set.mem_setOf_eq] at hc
  obtain ⟨k, hh, hm, hb⟩ := exists_edge_of_rayParity d c.1 c.2 hc
  refine Set.mem_prod.mpr ⟨?_, ?_⟩
  · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hm⟩)
  · rw [Set.mem_Ico]
    constructor
    · by_contra hlt
      push_neg at hlt
      exact absurd (rayParity_zero_of_lt_yInf d hclosed c.1 c.2 hlt) (by rw [hc]; decide)
    · exact lt_of_lt_of_le hb (le_ySup d k)


noncomputable def interiorCells (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) :
    Finset (ℤ × ℤ) := (interiorSet_finite d hclosed).toFinset

theorem mem_interiorCells (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (c : ℤ × ℤ) :
    c ∈ interiorCells d hclosed ↔ rayParity d c.1 c.2 = 1 := by
  unfold interiorCells
  rw [Set.Finite.mem_toFinset]
  rfl

end StatMech.Onsager.InteriorCells
