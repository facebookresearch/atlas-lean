/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice`

Computes the adjacency of `StatMech.Lattice.hypercubicLattice d` for `d = 1` and `d = 2` (unit
steps are edges; the origin, diagonal steps, and steps of length two are not), membership in boxes
and their vertex boundary, and the edge boundary of the origin. Instantiates `box_finite` and
`iUnion_box` at `d = 2` and derives that the box `[-1, 1]^2` has a finite neighbourhood of the
origin and that every site lies in some box.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.HypercubicLattice

open _root_.StatMech _root_.StatMech.Lattice

-- In `ℤ¹`, `0` and `1` are neighbours.
example : (hypercubicLattice 1).Adj ![0] ![1] := by
  simp

-- In `ℤ¹`, `0` and `2` are not neighbours.
example : ¬ (hypercubicLattice 1).Adj ![0] ![2] := by
  simp

-- In `ℤ²`, a horizontal unit step is an edge.
example : (hypercubicLattice 2).Adj ![0, 0] ![1, 0] := by
  simp [Fin.sum_univ_two]

-- In `ℤ²`, a vertical unit step in the negative direction is an edge.
example : (hypercubicLattice 2).Adj ![3, 5] ![3, 4] := by
  simp [Fin.sum_univ_two]

-- In `ℤ²`, a diagonal step is not an edge (its `ℓ¹` length is two).
example : ¬ (hypercubicLattice 2).Adj ![0, 0] ![1, 1] := by
  simp [Fin.sum_univ_two]

-- The graph is loopless.
example (x : Site 2) : ¬ (hypercubicLattice 2).Adj x x := (hypercubicLattice 2).loopless.irrefl x

-- In `ℤ⁰` there are no edges: the `ℓ¹` distance is always zero.
example (x y : Site 0) : ¬ (hypercubicLattice 0).Adj x y := by
  simp

-- Membership in the box `[-1, 1]^2`.
example : (![1, -1] : Site 2) ∈ box 2 1 := by
  intro i; fin_cases i <;> simp

example : (![2, 0] : Site 2) ∉ box 2 1 := by
  intro h; have := h 0; simp at this

-- `![1, 0]` lies on the vertex boundary of `[-1, 1]^2`, the origin does not.
example : (![1, 0] : Site 2) ∈ vertexBoundary 2 1 := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · intro h; have := h 0; simp at this

example : (![0, 0] : Site 2) ∉ vertexBoundary 2 1 := by
  rintro ⟨_, h⟩; exact h (fun i => by fin_cases i <;> simp)

-- The edge `(0, e₁)` lies in the edge boundary of `{0}`, in both orientations.
example : ((![0, 0] : Site 2), (![1, 0] : Site 2)) ∈ edgeBoundary 2 {![0, 0]} := by
  refine ⟨by simp [Fin.sum_univ_two], ?_⟩
  simp

example : ((![1, 0] : Site 2), (![0, 0] : Site 2)) ∈ edgeBoundary 2 {![0, 0]} :=
  edgeBoundary_symm (by refine ⟨by simp [Fin.sum_univ_two], ?_⟩; simp)

-- `box_finite`: the box `[-3, 3]^2` is finite, so its sites form a `Finset`.
example : ∃ s : Finset (Site 2), ↑s = box 2 3 := ⟨(box_finite 2 3).toFinset, by simp⟩

-- `iUnion_box`: the site `(7, -2)` lies in some box, and `box_mono` moves it to any larger box.
example : ∃ n, (![7, -2] : Site 2) ∈ box 2 n := by
  have h : (![7, -2] : Site 2) ∈ ⋃ n, box 2 n := by rw [iUnion_box]; trivial
  simpa using h

example : (![7, -2] : Site 2) ∈ box 2 8 :=
  box_mono 2 (by norm_num : 7 ≤ 8) (fun i => by fin_cases i <;> simp)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
