/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Ring.Nat

/-!
# Corners of a finite set of unit cells

A finite set `S` of unit cells of `ℤ²` (cell `c` is the square with lower-left corner `c`) has
vertices `cellVerts S`, the corners of its cells. For a lattice point `v`, `cornerCount S v ∈
{0, …, 4}` is the number of cells of `S` having `v` as a corner. Double counting gives
`∑ v, cornerCount S v = 4 * S.card`.

## Main definitions

* `StatMech.Onsager.CellCount.cornersOf`: the four corners of a cell.
* `StatMech.Onsager.CellCount.cornerCount`: the number of cells of `S` at a lattice point.
* `StatMech.Onsager.CellCount.cellVerts`: the set of corners of cells of `S`.

## Main results

* `StatMech.Onsager.CellCount.cornerCount_le_four`.
* `StatMech.Onsager.CellCount.sum_cornerCount`.
-/

@[expose] public section

namespace StatMech.Onsager.CellCount

open Finset

/-- The four corners of the unit cell with lower-left corner `c`. -/
def cornersOf (c : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {c, (c.1 + 1, c.2), (c.1, c.2 + 1), (c.1 + 1, c.2 + 1)}

/-- The number of cells of `S` having the lattice point `v` as a corner. -/
def cornerCount (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : ℕ :=
  (S.filter (fun c => v ∈ cornersOf c)).card

/-- The vertices of the cell complex `S`: all corners of its cells. -/
def cellVerts (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S.biUnion cornersOf

/-- A cell has four distinct corners. -/
theorem cornersOf_card (c : ℤ × ℤ) : (cornersOf c).card = 4 := by
  unfold cornersOf
  rw [Finset.card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp only [mem_singleton, Prod.ext_iff]; omega),
      card_singleton]

/-- `v` is a corner of `c` iff `c` is one of the four cells around `v`. -/
theorem mem_cornersOf_iff (c v : ℤ × ℤ) :
    v ∈ cornersOf c ↔
      c = v ∨ c = (v.1 - 1, v.2) ∨ c = (v.1, v.2 - 1) ∨ c = (v.1 - 1, v.2 - 1) := by
  obtain ⟨cx, cy⟩ := c
  obtain ⟨vx, vy⟩ := v
  unfold cornersOf
  simp only [mem_insert, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega

/-- The four cells having `v` as a corner. -/
private def candCells (v : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {v, (v.1 - 1, v.2), (v.1, v.2 - 1), (v.1 - 1, v.2 - 1)}

/-- At most four cells meet at a lattice point. -/
theorem cornerCount_le_four (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    cornerCount S v ≤ 4 := by
  unfold cornerCount
  have hsub : S.filter (fun c => v ∈ cornersOf c) ⊆ candCells v := by
    intro c hc
    rw [mem_filter, mem_cornersOf_iff] at hc
    unfold candCells
    simp only [mem_insert, mem_singleton]
    tauto
  refine (card_le_card hsub).trans ?_
  unfold candCells
  refine (card_insert_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_insert_le _ _) 1).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (card_insert_le _ _) 1) 1).trans ?_
  simp

/-- Double counting of cell–corner incidences: `∑ v, cornerCount S v = 4 * S.card`. -/
theorem sum_cornerCount (S : Finset (ℤ × ℤ)) :
    ∑ v ∈ cellVerts S, cornerCount S v = 4 * S.card := by
  unfold cornerCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have key : ∀ c ∈ S, (∑ v ∈ cellVerts S, if v ∈ cornersOf c then 1 else 0) = 4 := by
    intro c hc
    rw [← Finset.sum_filter]
    have hfe : (cellVerts S).filter (fun v => v ∈ cornersOf c) = cornersOf c := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro hv
        exact ⟨Finset.mem_biUnion.mpr ⟨c, hc, hv⟩, hv⟩
    rw [hfe, Finset.sum_const, smul_eq_mul, mul_one]
    exact cornersOf_card c
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul, mul_comm]

end StatMech.Onsager.CellCount
