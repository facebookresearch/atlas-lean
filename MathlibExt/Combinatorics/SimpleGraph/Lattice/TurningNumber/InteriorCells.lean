/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.JordanParity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCrossingV
import Mathlib.Data.Int.Interval

/-!
# The finite set of interior cells

The interior of a closed lattice walk, defined by the even-odd rule (cells with ray parity `1`),
is a finite set of cells: an inside cell lies below some horizontal step of the walk and above its
lowest vertex.

## Main definitions

* `StatMech.Onsager.InteriorCells.interiorSet`: the cells with ray parity `1`.
* `StatMech.Onsager.InteriorCells.yInf`, `StatMech.Onsager.InteriorCells.ySup`: the minimal and
  maximal heights of the walk.
* `StatMech.Onsager.InteriorCells.interiorCells`: the interior as a `Finset`.

## Main results

* `StatMech.Onsager.InteriorCells.interiorSet_finite`.
* `StatMech.Onsager.InteriorCells.mem_interiorCells`.
-/

@[expose] public section

namespace StatMech.Onsager.InteriorCells

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.WalkCrossingV StatMech.Onsager.JordanParity

variable {n : ℕ} [NeZero n]

/-- The cells inside the walk by the even-odd rule: those with ray parity `1`. -/
def interiorSet (d : Fin n → Fin 4) : Set (ℤ × ℤ) := {c | rayParity d c.1 c.2 = 1}

/-- The minimal height of a vertex of the walk. -/
noncomputable def yInf (d : Fin n → Fin 4) : ℤ :=
  Finset.univ.inf' Finset.univ_nonempty (fun k => (pos d k).2)

/-- The maximal height of a vertex of the walk. -/
noncomputable def ySup (d : Fin n → Fin 4) : ℤ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k => (pos d k).2)

theorem yInf_le (d : Fin n → Fin 4) (k : Fin n) : yInf d ≤ (pos d k).2 :=
  Finset.inf'_le (fun k => (pos d k).2) (Finset.mem_univ k)

theorem le_ySup (d : Fin n → Fin 4) (k : Fin n) : (pos d k).2 ≤ ySup d :=
  Finset.le_sup' (fun k => (pos d k).2) (Finset.mem_univ k)

/-- An inside cell lies directly below some horizontal step of the walk. -/
theorem exists_edge_of_rayParity (d : Fin n → Fin 4) (a b : ℤ) (h : rayParity d a b = 1) :
    ∃ k : Fin n, isHorizEdge (d k) ∧ min ((pos d k).1) ((pos d (k + 1)).1) = a ∧
        b < (pos d k).2 := by
  by_contra hcon
  push Not at hcon
  have hz : upCross d a b = 0 := by
    unfold upCross
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _
    rintro ⟨hh, hm, hb⟩
    exact absurd hb (by have := hcon k hh hm; omega)
  rw [rayParity, hz] at h
  simp at h

/-- Cells below the walk are outside. -/
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

/-- A closed walk has finitely many inside cells. -/
theorem interiorSet_finite (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) :
    (interiorSet d).Finite := by
  apply Set.Finite.subset
    (Set.Finite.prod
      (Finset.univ.image (fun k => min ((pos d k).1) ((pos d (k + 1)).1))).finite_toSet
      (Set.finite_Ico (yInf d) (ySup d)))
  intro c hc
  simp only [interiorSet, Set.mem_ofPred_eq] at hc
  obtain ⟨k, hh, hm, hb⟩ := exists_edge_of_rayParity d c.1 c.2 hc
  refine Set.mem_prod.mpr ⟨?_, ?_⟩
  · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hm⟩)
  · rw [Set.mem_Ico]
    constructor
    · by_contra hlt
      push Not at hlt
      exact absurd (rayParity_zero_of_lt_yInf d hclosed c.1 c.2 hlt) (by rw [hc]; decide)
    · exact lt_of_lt_of_le hb (le_ySup d k)

/-- The finite set of cells inside a closed walk (ray parity `1`). See also
  `StatMech.Onsager.WalkCellRegion.interiorCells`, the bounded face of the walk; the two agree for
  simple walks without right turns (`StatMech.Onsager.UmlaufsatzFinal.interiorCells_bridge`). -/
noncomputable def interiorCells (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) :
    Finset (ℤ × ℤ) := (interiorSet_finite d hclosed).toFinset

theorem mem_interiorCells (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (c : ℤ × ℤ) :
    c ∈ interiorCells d hclosed ↔ rayParity d c.1 c.2 = 1 := by
  unfold interiorCells
  rw [Set.Finite.mem_toFinset]
  rfl

end StatMech.Onsager.InteriorCells
