/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellCount

/-!
# Corner defect and Euler characteristic of a set of unit cells

For a finite set `S` of unit cells, `cornerDiff S` is the number of vertices at which exactly one
cell of `S` meets (convex corners of the region) minus the number at which exactly three meet
(reflex corners): a discrete total curvature of the boundary. `eulerChar S = V - E + F` is the
Euler characteristic of the cell complex. This file gives the formulas for both under adding one
cell and computes them for a single cell (`4` and `1`).

## Main definitions

* `StatMech.Onsager.CellEuler.cornerDiff`: convex minus reflex corners.
* `StatMech.Onsager.CellEuler.cornerWeight`: the contribution `+1, 0, -1` of a vertex with `1`,
  `0, 2, 4`, `3` incident cells.
* `StatMech.Onsager.CellEuler.edgesOf`, `StatMech.Onsager.CellEuler.cellEdges`: edges of cells,
  encoded by their doubled midpoints.
* `StatMech.Onsager.CellEuler.eulerChar`: vertices minus edges plus cells.

## Main results

* `StatMech.Onsager.CellEuler.cornerDiff_eq_sum`, `StatMech.Onsager.CellEuler.cornerDiff_insert`.
* `StatMech.Onsager.CellEuler.eulerChar_insert`.
* `StatMech.Onsager.CellEuler.cornerDiff_singleton`,
  `StatMech.Onsager.CellEuler.eulerChar_singleton`.
-/

@[expose] public section

namespace StatMech.Onsager.CellEuler

open Finset StatMech.Onsager.CellCount

/-- The corner defect of `S`: the number of vertices with exactly one incident cell of `S` (convex
  corners) minus the number with exactly three (reflex corners). -/
def cornerDiff (S : Finset (ℤ × ℤ)) : ℤ :=
  ((cellVerts S).filter (fun v => cornerCount S v = 1)).card
    - ((cellVerts S).filter (fun v => cornerCount S v = 3)).card

/-- Adding a new cell `c` raises the corner count by one exactly at the corners of `c`. -/
theorem cornerCount_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∉ S) (v : ℤ × ℤ) :
    cornerCount (insert c S) v = cornerCount S v + (if v ∈ cornersOf c then 1 else 0) := by
  unfold cornerCount
  rw [Finset.filter_insert]
  by_cases h : v ∈ cornersOf c
  · rw [ite_eq_left h, ite_eq_left h,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_filter]; exact fun h' => hc h'.1)]
  · rw [ite_eq_right h, ite_eq_right h, add_zero]

/-- The vertices of `insert c S`. -/
theorem cellVerts_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    cellVerts (insert c S) = cornersOf c ∪ cellVerts S := by
  unfold cellVerts
  rw [Finset.biUnion_insert]

/-- The weight of a vertex with `k` incident cells in the corner defect: `1` if `k = 1`, `-1` if `k
  = 3`, and `0` otherwise. -/
def cornerWeight (k : ℕ) : ℤ := (if k = 1 then 1 else 0) - (if k = 3 then 1 else 0)

/-- A lattice point has an incident cell iff it is a vertex of `S`. -/
theorem cornerCount_pos_iff_mem (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    0 < cornerCount S v ↔ v ∈ cellVerts S := by
  unfold cornerCount cellVerts
  rw [Finset.card_pos]
  constructor
  · rintro ⟨c, hc⟩
    rw [Finset.mem_filter] at hc
    exact Finset.mem_biUnion.mpr ⟨c, hc.1, hc.2⟩
  · intro hv
    obtain ⟨c, hcS, hvc⟩ := Finset.mem_biUnion.mp hv
    exact ⟨c, Finset.mem_filter.mpr ⟨hcS, hvc⟩⟩

theorem cornerWeight_zero : cornerWeight 0 = 0 := by unfold cornerWeight; decide

/-- The corner defect as a sum of vertex weights. -/
theorem cornerDiff_eq_sum (S : Finset (ℤ × ℤ)) :
    cornerDiff S = ∑ v ∈ cellVerts S, cornerWeight (cornerCount S v) := by
  unfold cornerDiff cornerWeight
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]

/-- Change of the corner defect when a new cell is added. -/
theorem cornerDiff_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∉ S) :
    cornerDiff (insert c S)
      = cornerDiff S + ∑ v ∈ cornersOf c,
          (cornerWeight (cornerCount S v + 1) - cornerWeight (cornerCount S v)) := by
  have hsub : cornerDiff S
      = ∑ v ∈ cornersOf c ∪ cellVerts S, cornerWeight (cornerCount S v) := by
    rw [cornerDiff_eq_sum]
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hvnot
    have hz : cornerCount S v = 0 := by
      by_contra h
      exact hvnot ((cornerCount_pos_iff_mem S v).mp (Nat.pos_of_ne_zero h))
    rw [hz, cornerWeight_zero]
  have hexpand :
      ∑ v ∈ cornersOf c ∪ cellVerts S,
          (if v ∈ cornersOf c then
            cornerWeight (cornerCount S v + 1) - cornerWeight (cornerCount S v) else 0)
        = ∑ v ∈ cornersOf c,
          (cornerWeight (cornerCount S v + 1) - cornerWeight (cornerCount S v)) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_left]
  rw [cornerDiff_eq_sum, cellVerts_insert, hsub, ← hexpand, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [cornerCount_insert S c hc v]
  by_cases h : v ∈ cornersOf c
  · simp only [ite_eq_left h]; ring
  · simp only [ite_eq_right h, add_zero]

theorem cornerCount_singleton_eq_one (c v : ℤ × ℤ) (hv : v ∈ cornersOf c) :
    cornerCount ({c} : Finset (ℤ × ℤ)) v = 1 := by
  unfold cornerCount
  rw [Finset.filter_singleton, ite_eq_left hv, Finset.card_singleton]

theorem cornerCount_singleton_eq_zero (c v : ℤ × ℤ) (hv : v ∉ cornersOf c) :
    cornerCount ({c} : Finset (ℤ × ℤ)) v = 0 := by
  unfold cornerCount
  rw [Finset.filter_singleton, ite_eq_right hv, Finset.card_empty]

theorem cellVerts_singleton (c : ℤ × ℤ) : cellVerts ({c} : Finset (ℤ × ℤ)) = cornersOf c := by
  unfold cellVerts; rw [Finset.singleton_biUnion]

/-- A single cell has corner defect `4`. -/
theorem cornerDiff_singleton (c : ℤ × ℤ) : cornerDiff ({c} : Finset (ℤ × ℤ)) = 4 := by
  unfold cornerDiff
  rw [cellVerts_singleton]
  have hconv : (cornersOf c).filter (fun v => cornerCount ({c} : Finset (ℤ × ℤ)) v = 1)
      = cornersOf c := by
    apply Finset.filter_true_of_mem
    intro v hv
    exact cornerCount_singleton_eq_one c v hv
  have hrefl : (cornersOf c).filter (fun v => cornerCount ({c} : Finset (ℤ × ℤ)) v = 3)
      = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v hv
    rw [cornerCount_singleton_eq_one c v hv]
    decide
  rw [hconv, hrefl, cornersOf_card, Finset.card_empty]
  decide

/-- The corner count at `v` counts the cells of `S` among the four cells around `v`. -/
theorem cornerCount_eq_inter (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    cornerCount S v
      = (S ∩ ({v, (v.1 - 1, v.2), (v.1, v.2 - 1), (v.1 - 1, v.2 - 1)} : Finset (ℤ × ℤ))).card := by
  unfold cornerCount
  congr 1
  ext c'
  rw [Finset.mem_filter, Finset.mem_inter, mem_cornersOf_iff]
  simp only [mem_insert, mem_singleton]

/-- The four edges of cell `c`, each encoded by twice its midpoint. -/
def edgesOf (c : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {(2 * c.1 + 1, 2 * c.2), (2 * c.1 + 1, 2 * c.2 + 2),
    (2 * c.1, 2 * c.2 + 1), (2 * c.1 + 2, 2 * c.2 + 1)}

/-- The edges of the cell complex `S`, encoded by doubled midpoints. -/
def cellEdges (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := S.biUnion edgesOf

/-- The Euler characteristic `V - E + F` of the closed cell complex formed by the cells of `S`. -/
def eulerChar (S : Finset (ℤ × ℤ)) : ℤ :=
  ((cellVerts S).card : ℤ) - (cellEdges S).card + S.card

theorem edgesOf_card (c : ℤ × ℤ) : (edgesOf c).card = 4 := by
  unfold edgesOf
  rw [Finset.card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp only [mem_singleton, Prod.ext_iff]; omega),
      card_singleton]

theorem cellEdges_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    cellEdges (insert c S) = edgesOf c ∪ cellEdges S := by
  unfold cellEdges; rw [Finset.biUnion_insert]

theorem cellEdges_singleton (c : ℤ × ℤ) : cellEdges ({c} : Finset (ℤ × ℤ)) = edgesOf c := by
  unfold cellEdges; rw [Finset.singleton_biUnion]

/-- A single cell has Euler characteristic `1`. -/
theorem eulerChar_singleton (c : ℤ × ℤ) : eulerChar ({c} : Finset (ℤ × ℤ)) = 1 := by
  unfold eulerChar
  rw [cellVerts_singleton, cellEdges_singleton, cornersOf_card, edgesOf_card, Finset.card_singleton]
  ring

private theorem card_union_sub (A B : Finset (ℤ × ℤ)) :
    ((A ∪ B).card : ℤ) - B.card = ((A \ B).card : ℤ) := by
  have hEq : A ∪ B = B ∪ (A \ B) := by
    rw [Finset.union_sdiff_self_eq_union, Finset.union_comm]
  rw [hEq, Finset.card_union_of_disjoint (Finset.sdiff_disjoint).symm]
  push_cast; ring

theorem eulerChar_insert_vertexDelta (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    ((cellVerts (insert c S)).card : ℤ) - (cellVerts S).card
      = ((cornersOf c \ cellVerts S).card : ℤ) := by
  rw [cellVerts_insert]; exact card_union_sub (cornersOf c) (cellVerts S)

theorem eulerChar_insert_edgeDelta (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    ((cellEdges (insert c S)).card : ℤ) - (cellEdges S).card
      = ((edgesOf c \ cellEdges S).card : ℤ) := by
  rw [cellEdges_insert]; exact card_union_sub (edgesOf c) (cellEdges S)

/-- Change of the Euler characteristic when a new cell is added: new vertices minus new edges plus
  one. -/
theorem eulerChar_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∉ S) :
    eulerChar (insert c S)
      = eulerChar S + (((cornersOf c \ cellVerts S).card : ℤ)
          - (edgesOf c \ cellEdges S).card + 1) := by
  have hV := eulerChar_insert_vertexDelta S c
  have hE := eulerChar_insert_edgeDelta S c
  unfold eulerChar
  rw [Finset.card_insert_of_notMem hc]
  push_cast at hV hE ⊢
  linarith [hV, hE]

end StatMech.Onsager.CellEuler
