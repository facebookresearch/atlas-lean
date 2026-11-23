/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellLocalChange
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellPinch

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring.RingNF

/-!
# The cell Gauss–Bonnet formula

For every finite set `S` of unit cells of `ℤ²`, the number of convex corners minus the number of
reflex corners equals four times the Euler characteristic plus twice the number of pinch points:

  `cornerDiff S = 4 * eulerChar S + 2 * pinchCount S`.

This is a discrete Gauss–Bonnet theorem: each convex corner carries turning `+π/2`, each reflex
corner `-π/2`, and the total turning of the boundary of a region is `2π` times its Euler
characteristic. The proof is by induction on `S`, adding one cell at a time and using the local
identity `StatMech.Onsager.CellGaussBonnet.localIdentity_corrected`.

## Main results

* `StatMech.Onsager.CellGaussBonnetGlobal.cornerDiff_eq`.
-/

@[expose] public section

namespace StatMech.Onsager.CellGaussBonnetGlobal

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellGaussBonnet StatMech.Onsager.CellConnect
  StatMech.Onsager.CellConnect2 StatMech.Onsager.CellPinch

private theorem mem_ins_iff (S : Finset (ℤ × ℤ)) (x y a b : ℤ) (hne : (a, b) ≠ (x, y)) :
    ((a, b) : ℤ × ℤ) ∈ insert ((x, y) : ℤ × ℤ) S ↔ (a, b) ∈ S := by
  rw [Finset.mem_insert]; tauto

/-- Change of the pinch indicator at the bottom-left corner of a new cell. -/
theorem pinch_diff_BL (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    pinchW (insert (x, y) S) (x, y) - pinchW S (x, y)
      = (if ((x - 1, y - 1) ∈ S ∧ (x - 1, y) ∉ S ∧ (x, y - 1) ∉ S) then (1 : ℤ) else 0)
        - (if ((x - 1, y) ∈ S ∧ (x, y - 1) ∈ S ∧ (x - 1, y - 1) ∉ S) then (1 : ℤ) else 0) := by
  unfold pinchW pinchAt
  have h1 := mem_ins_iff S x y (x - 1) (y - 1) (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h2 := mem_ins_iff S x y (x - 1) y (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h3 := mem_ins_iff S x y x (y - 1) (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h0 : ((x, y) : ℤ × ℤ) ∈ insert ((x, y) : ℤ × ℤ) S := Finset.mem_insert_self _ _
  simp only [h0, h1, h2, h3, hc]
  by_cases hW : (x - 1, y) ∈ S <;> by_cases hSo : (x, y - 1) ∈ S <;>
    by_cases hSW : (x - 1, y - 1) ∈ S <;> simp_all

/-- Change of the pinch indicator at the bottom-right corner of a new cell. -/
theorem pinch_diff_BR (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    pinchW (insert (x, y) S) (x + 1, y) - pinchW S (x + 1, y)
      = (if ((x + 1, y - 1) ∈ S ∧ (x + 1, y) ∉ S ∧ (x, y - 1) ∉ S) then (1 : ℤ) else 0)
        - (if ((x + 1, y) ∈ S ∧ (x, y - 1) ∈ S ∧ (x + 1, y - 1) ∉ S) then (1 : ℤ) else 0) := by
  unfold pinchW pinchAt
  have h1 := mem_ins_iff S x y (x + 1) y (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h2 := mem_ins_iff S x y (x + 1) (y - 1) (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h3 := mem_ins_iff S x y x (y - 1) (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h0 : ((x, y) : ℤ × ℤ) ∈ insert ((x, y) : ℤ × ℤ) S := Finset.mem_insert_self _ _
  have e1 : ((x + 1, y) : ℤ × ℤ).1 - 1 = x := by simp
  have e2 : ((x + 1, y) : ℤ × ℤ).2 = y := by simp
  simp only [show x + 1 - 1 = x from by ring,
    h0, h1, h2, h3, hc]
  by_cases hE : (x + 1, y) ∈ S <;> by_cases hSo : (x, y - 1) ∈ S <;>
    by_cases hSE : (x + 1, y - 1) ∈ S <;> simp_all

/-- Change of the pinch indicator at the top-left corner of a new cell. -/
theorem pinch_diff_TL (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    pinchW (insert (x, y) S) (x, y + 1) - pinchW S (x, y + 1)
      = (if ((x - 1, y + 1) ∈ S ∧ (x, y + 1) ∉ S ∧ (x - 1, y) ∉ S) then (1 : ℤ) else 0)
        - (if ((x, y + 1) ∈ S ∧ (x - 1, y) ∈ S ∧ (x - 1, y + 1) ∉ S) then (1 : ℤ) else 0) := by
  unfold pinchW pinchAt
  have h1 := mem_ins_iff S x y (x - 1) (y + 1) (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h2 := mem_ins_iff S x y (x - 1) y (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h3 := mem_ins_iff S x y x (y + 1) (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h0 : ((x, y) : ℤ × ℤ) ∈ insert ((x, y) : ℤ × ℤ) S := Finset.mem_insert_self _ _
  simp only [show ((x, y + 1) : ℤ × ℤ).2 - 1 = y from by ring, h0, h1, h2, h3, hc]
  by_cases hN : (x, y + 1) ∈ S <;> by_cases hW : (x - 1, y) ∈ S <;>
    by_cases hNW : (x - 1, y + 1) ∈ S <;> simp_all

/-- Change of the pinch indicator at the top-right corner of a new cell. -/
theorem pinch_diff_TR (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    pinchW (insert (x, y) S) (x + 1, y + 1) - pinchW S (x + 1, y + 1)
      = (if ((x + 1, y + 1) ∈ S ∧ (x, y + 1) ∉ S ∧ (x + 1, y) ∉ S) then (1 : ℤ) else 0)
        - (if ((x, y + 1) ∈ S ∧ (x + 1, y) ∈ S ∧ (x + 1, y + 1) ∉ S) then (1 : ℤ) else 0) := by
  unfold pinchW pinchAt
  have h1 := mem_ins_iff S x y (x + 1) (y + 1) (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h2 := mem_ins_iff S x y (x + 1) y (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h3 := mem_ins_iff S x y x (y + 1) (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h0 : ((x, y) : ℤ × ℤ) ∈ insert ((x, y) : ℤ × ℤ) S := Finset.mem_insert_self _ _
  simp only [show ((x + 1, y + 1) : ℤ × ℤ).1 - 1 = x from by ring,
    show ((x + 1, y + 1) : ℤ × ℤ).2 - 1 = y from by ring, h0, h1, h2, h3, hc]
  by_cases hN : (x, y + 1) ∈ S <;> by_cases hE : (x + 1, y) ∈ S <;>
    by_cases hNE : (x + 1, y + 1) ∈ S <;> simp_all

/-- The change of the pinch count when a cell is added, in terms of its eight neighbours. -/
theorem pinch_jump_sum (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    (∑ v ∈ cornersOf (x, y), (pinchW (insert (x, y) S) v - pinchW S v))
      = pinchDelta (decide ((x + 1, y) ∈ S)) (decide ((x - 1, y) ∈ S)) (decide ((x, y + 1) ∈ S))
          (decide ((x, y - 1) ∈ S)) (decide ((x + 1, y + 1) ∈ S)) (decide ((x - 1, y + 1) ∈ S))
          (decide ((x + 1, y - 1) ∈ S)) (decide ((x - 1, y - 1) ∈ S)) := by
  rw [show cornersOf (x, y) = {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)} from rfl,
      Finset.sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp only [mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_singleton,
      pinch_diff_BL S x y hc, pinch_diff_BR S x y hc, pinch_diff_TL S x y hc,
      pinch_diff_TR S x y hc]
  unfold pinchDelta bI
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases hE : (x + 1, y) ∈ S <;> by_cases hW : (x - 1, y) ∈ S <;>
    by_cases hN : (x, y + 1) ∈ S <;> by_cases hSo : (x, y - 1) ∈ S <;>
    by_cases hNE : (x + 1, y + 1) ∈ S <;> by_cases hNW : (x - 1, y + 1) ∈ S <;>
    by_cases hSE : (x + 1, y - 1) ∈ S <;> by_cases hSW : (x - 1, y - 1) ∈ S <;> simp_all

/-- Cell Gauss–Bonnet formula: for every finite set of unit cells, convex corners minus reflex
  corners equals four times the Euler characteristic plus twice the number of pinch points. -/
theorem cornerDiff_eq (S : Finset (ℤ × ℤ)) :
    cornerDiff S = 4 * eulerChar S + 2 * pinchCount S := by
  induction S using Finset.induction with
  | empty =>
    simp only [cornerDiff, eulerChar, pinchCount, cellVerts, cellEdges,
      Finset.biUnion_empty, Finset.card_empty, Finset.filter_empty, Finset.sum_empty]
    ring
  | @insert c S hc ih =>
    obtain ⟨x, y⟩ := c
    rw [cornerDiff_insert S (x, y) hc, cornerDiff_jump_sum S x y hc,
        eulerChar_insert S (x, y) hc,
        pinchCount_insert S (x, y) hc, pinch_jump_sum S x y hc, ih,
        sdiff_cellVerts_card_eq_deltaV S x y hc, sdiff_cellEdges_card_eq_deltaE S x y hc]
    have hloc := localIdentity_corrected (decide ((x + 1, y) ∈ S)) (decide ((x - 1, y) ∈ S))
      (decide ((x, y + 1) ∈ S)) (decide ((x, y - 1) ∈ S)) (decide ((x + 1, y + 1) ∈ S))
      (decide ((x - 1, y + 1) ∈ S)) (decide ((x + 1, y - 1) ∈ S)) (decide ((x - 1, y - 1) ∈ S))
    unfold rhsCorrected rhsStated at hloc
    rw [hloc]
    ring

end StatMech.Onsager.CellGaussBonnetGlobal
