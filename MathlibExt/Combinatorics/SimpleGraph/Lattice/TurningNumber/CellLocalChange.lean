/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellCornerCountLocal
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnetLocal

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring.RingNF

/-!
# Local changes of corner defect, vertices and edges

When a cell `(x, y) ∉ S` is added to `S`, the changes of the corner defect, of the number of
vertices and of the number of edges depend only on which of its eight neighbouring cells lie in
`S`. This file expresses them through the Boolean functions `lhsLocal`, `deltaV`, `deltaE` of
`MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnet`.

## Main results

* `StatMech.Onsager.CellConnect2.cornerDiff_jump_sum`: the change of the corner defect.
* `StatMech.Onsager.CellConnect2.sdiff_cellVerts_card_eq_deltaV`: the number of new vertices.
* `StatMech.Onsager.CellConnect2.sdiff_cellEdges_card_eq_deltaE`: the number of new edges.
-/

@[expose] public section

namespace StatMech.Onsager.CellConnect2

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellGaussBonnet StatMech.Onsager.CellConnect

/-- `cornerWeight` agrees with its integer version `icw`. -/
theorem cornerWeight_eq_icw (m : ℕ) : cornerWeight m = icw (m : ℤ) := by
  unfold cornerWeight icw
  split_ifs <;> omega

/-- The change of a vertex weight when one more cell becomes incident. -/
theorem cornerWeight_jump (m : ℕ) :
    cornerWeight (m + 1) - cornerWeight m = ijump (m : ℤ) := by
  unfold ijump
  rw [cornerWeight_eq_icw, cornerWeight_eq_icw]
  push_cast
  ring

/-- The indicator `bI` of a decided proposition. -/
theorem bI_decide (p : Prop) [Decidable p] : bI (decide p) = if p then 1 else 0 := by
  unfold bI
  by_cases h : p <;> simp [h]

/-- The change of the corner defect when the cell `(x, y)` is added, in terms of its eight
  neighbours. -/
theorem cornerDiff_jump_sum (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    (∑ v ∈ cornersOf (x, y),
        (cornerWeight (cornerCount S v + 1) - cornerWeight (cornerCount S v)))
      = lhsLocal (decide ((x + 1, y) ∈ S)) (decide ((x - 1, y) ∈ S)) (decide ((x, y + 1) ∈ S))
          (decide ((x, y - 1) ∈ S)) (decide ((x + 1, y + 1) ∈ S)) (decide ((x - 1, y + 1) ∈ S))
          (decide ((x + 1, y - 1) ∈ S)) (decide ((x - 1, y - 1) ∈ S)) := by
  have hexp : cornersOf (x, y) = {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)} := rfl
  rw [hexp]
  rw [Finset.sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp only [mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_singleton]
  rw [cornerWeight_jump, cornerWeight_jump, cornerWeight_jump, cornerWeight_jump,
      cornerCount_BL S x y hc, cornerCount_BR S x y hc, cornerCount_TL S x y hc,
      cornerCount_TR S x y hc]
  unfold lhsLocal bI
  simp only [decide_eq_true_eq]
  ring

/-- A lattice point is not a vertex of `S` iff no cell of `S` is incident to it. -/
theorem notMem_cellVerts_iff_cornerCount_zero (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    v ∉ cellVerts S ↔ cornerCount S v = 0 := by
  rw [← cornerCount_pos_iff_mem]; omega

/-- The size of `s \ t` as a sum of indicators. -/
theorem card_sdiff_eq_sum (s t : Finset (ℤ × ℤ)) :
    ((s \ t).card : ℤ) = ∑ v ∈ s, (if v ∉ t then (1 : ℤ) else 0) := by
  rw [Finset.sum_boole, Finset.sdiff_eq_filter]

/-- The number of new vertices when the cell `(x, y)` is added. -/
theorem sdiff_cellVerts_card_eq_deltaV (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    ((cornersOf (x, y) \ cellVerts S).card : ℤ)
      = deltaV (decide ((x + 1, y) ∈ S)) (decide ((x - 1, y) ∈ S)) (decide ((x, y + 1) ∈ S))
          (decide ((x, y - 1) ∈ S)) (decide ((x + 1, y + 1) ∈ S)) (decide ((x - 1, y + 1) ∈ S))
          (decide ((x + 1, y - 1) ∈ S)) (decide ((x - 1, y - 1) ∈ S)) := by
  have hkey : ∀ v : ℤ × ℤ,
      (if v ∉ cellVerts S then (1 : ℤ) else 0) = isZero (cornerCount S v : ℤ) := by
    intro v
    unfold isZero
    by_cases h : cornerCount S v = 0
    · rw [ite_eq_left ((notMem_cellVerts_iff_cornerCount_zero S v).mpr h),
        ite_eq_left (by exact_mod_cast h)]
    · rw [ite_eq_right (fun hn => h ((notMem_cellVerts_iff_cornerCount_zero S v).mp hn)),
          ite_eq_right (by exact_mod_cast h)]
  rw [card_sdiff_eq_sum,
      show cornersOf (x, y) = {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)} from rfl,
      Finset.sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp only [mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_singleton]
  simp only [hkey]
  rw [cornerCount_BL S x y hc, cornerCount_BR S x y hc, cornerCount_TL S x y hc,
      cornerCount_TR S x y hc]
  unfold deltaV bI
  simp only [decide_eq_true_eq]
  ring

/-- The horizontal edge with doubled midpoint `(2x + 1, 2y)` belongs to `S` iff one of the two cells
  it bounds does. -/
theorem mem_cellEdges_bottom (S : Finset (ℤ × ℤ)) (x y : ℤ) :
    ((2 * x + 1, 2 * y) : ℤ × ℤ) ∈ cellEdges S ↔ (x, y) ∈ S ∨ (x, y - 1) ∈ S := by
  simp only [cellEdges, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨cx, cy⟩, hcS, hmem⟩
    simp only [edgesOf, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [show cx = x by omega, show cy = y by omega] at hcS; exact hcS
    · right; rw [show cx = x by omega, show cy = y - 1 by omega] at hcS; exact hcS
    · omega
    · omega
  · rintro (h | h)
    · exact ⟨(x, y), h, by
        dsimp only [edgesOf]
        simp only [mem_insert, mem_singleton, Prod.mk.injEq, true_and, true_or]⟩
    · exact ⟨(x, y - 1), h, by
        dsimp only [edgesOf]
        simp only [mem_insert, mem_singleton, Prod.mk.injEq, true_and]; try omega⟩

/-- The horizontal edge with doubled midpoint `(2x + 1, 2y + 2)` belongs to `S` iff one of the two
  cells it bounds does. -/
theorem mem_cellEdges_top (S : Finset (ℤ × ℤ)) (x y : ℤ) :
    ((2 * x + 1, 2 * y + 2) : ℤ × ℤ) ∈ cellEdges S ↔ (x, y) ∈ S ∨ (x, y + 1) ∈ S := by
  simp only [cellEdges, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨cx, cy⟩, hcS, hmem⟩
    simp only [edgesOf, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; rw [show cx = x by omega, show cy = y + 1 by omega] at hcS; exact hcS
    · left; rw [show cx = x by omega, show cy = y by omega] at hcS; exact hcS
    · omega
    · omega
  · rintro (h | h)
    · exact ⟨(x, y), h, by
        dsimp only [edgesOf]
        simp only [mem_insert, mem_singleton, Prod.mk.injEq, true_and, true_or, or_true]⟩
    · exact ⟨(x, y + 1), h, by
        dsimp only [edgesOf]
        simp only [mem_insert, mem_singleton, Prod.mk.injEq, true_and]; try omega⟩

/-- The vertical edge with doubled midpoint `(2x, 2y + 1)` belongs to `S` iff one of the two cells
  it bounds does. -/
theorem mem_cellEdges_left (S : Finset (ℤ × ℤ)) (x y : ℤ) :
    ((2 * x, 2 * y + 1) : ℤ × ℤ) ∈ cellEdges S ↔ (x, y) ∈ S ∨ (x - 1, y) ∈ S := by
  simp only [cellEdges, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨cx, cy⟩, hcS, hmem⟩
    simp only [edgesOf, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · omega
    · left; rw [show cx = x by omega, show cy = y by omega] at hcS; exact hcS
    · right; rw [show cx = x - 1 by omega, show cy = y by omega] at hcS; exact hcS
  · rintro (h | h)
    · exact ⟨(x, y), h, by
        dsimp only [edgesOf]
        simp only [mem_insert, mem_singleton, Prod.mk.injEq, and_true, true_or, or_true]⟩
    · exact ⟨(x - 1, y), h, by
        dsimp only [edgesOf]
        simp only [mem_insert, mem_singleton, Prod.mk.injEq, and_true]; try omega⟩

/-- The vertical edge with doubled midpoint `(2x + 2, 2y + 1)` belongs to `S` iff one of the two
  cells it bounds does. -/
theorem mem_cellEdges_right (S : Finset (ℤ × ℤ)) (x y : ℤ) :
    ((2 * x + 2, 2 * y + 1) : ℤ × ℤ) ∈ cellEdges S ↔ (x, y) ∈ S ∨ (x + 1, y) ∈ S := by
  simp only [cellEdges, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨cx, cy⟩, hcS, hmem⟩
    simp only [edgesOf, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · omega
    · right; rw [show cx = x + 1 by omega, show cy = y by omega] at hcS; exact hcS
    · left; rw [show cx = x by omega, show cy = y by omega] at hcS; exact hcS
  · rintro (h | h)
    · exact ⟨(x, y), h, by
        dsimp only [edgesOf]
        simp only [mem_insert, mem_singleton, Prod.mk.injEq, and_true, or_true]⟩
    · exact ⟨(x + 1, y), h, by
        dsimp only [edgesOf]
        simp only [mem_insert, mem_singleton, Prod.mk.injEq, and_true]; try omega⟩

/-- The number of new edges when the cell `(x, y)` is added. -/
theorem sdiff_cellEdges_card_eq_deltaE (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    ((edgesOf (x, y) \ cellEdges S).card : ℤ)
      = deltaE (decide ((x + 1, y) ∈ S)) (decide ((x - 1, y) ∈ S)) (decide ((x, y + 1) ∈ S))
          (decide ((x, y - 1) ∈ S)) := by
  have hb : ((2 * x + 1, 2 * y) : ℤ × ℤ) ∉ cellEdges S ↔ (x, y - 1) ∉ S := by
    rw [mem_cellEdges_bottom]; tauto
  have ht : ((2 * x + 1, 2 * y + 2) : ℤ × ℤ) ∉ cellEdges S ↔ (x, y + 1) ∉ S := by
    rw [mem_cellEdges_top]; tauto
  have hl : ((2 * x, 2 * y + 1) : ℤ × ℤ) ∉ cellEdges S ↔ (x - 1, y) ∉ S := by
    rw [mem_cellEdges_left]; tauto
  have hr : ((2 * x + 2, 2 * y + 1) : ℤ × ℤ) ∉ cellEdges S ↔ (x + 1, y) ∉ S := by
    rw [mem_cellEdges_right]; tauto
  rw [card_sdiff_eq_sum,
      show edgesOf (x, y)
        = {(2 * x + 1, 2 * y), (2 * x + 1, 2 * y + 2), (2 * x, 2 * y + 1), (2 * x + 2, 2 * y + 1)}
        from rfl,
      Finset.sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp only [mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_singleton]
  rw [if_congr hb rfl rfl, if_congr ht rfl rfl, if_congr hl rfl rfl, if_congr hr rfl rfl]
  unfold deltaE bI
  simp only [decide_eq_true_eq]
  by_cases hE : (x + 1, y) ∈ S <;> by_cases hW : (x - 1, y) ∈ S <;>
    by_cases hN : (x, y + 1) ∈ S <;> by_cases hSo : (x, y - 1) ∈ S <;>
    simp_all

end StatMech.Onsager.CellConnect2
