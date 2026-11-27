/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.DiscreteJordanSeparationVariant

/-!
# Tests for `MathlibExt.Probability.Percolation.DiscreteJordanSeparationVariant`

* `djfx_faceBoundaryGraph_edgeCycle` (every edge of a face-boundary graph lies on a cycle) for
  `K = {(0,0)}`: the edge between the faces `(0,0)` and `(-1,0)` lies on a cycle.
* The counterexample set `djfx_bowtie`: membership in coordinates; the edge-cycle theorem
  applies to it too, while the corrected separation property fails
  (`not_djfx_DiscreteJordanSeparation'`). No test assumes `djfx_DiscreteJordanSeparation'`.
-/

@[expose] public section

open SimpleGraph StatMech.Lattice StatMech.Percolation

namespace MathlibExtTest.StatMech.Probability.Percolation.DiscreteJordanSeparationVariant

/-- The faces `(0,0)` and `(-1,0)` are adjacent in the face-boundary graph of `{(0,0)}`: they
share the primal edge from `(0,0)` to `(0,1)`, which leaves the set. -/
theorem adj_single : (faceBoundaryGraph ({![0, 0]} : Set (Site 2))).Adj ![0, 0] ![-1, 0] := by
  refine ⟨?_, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · unfold sharedPrimalEdge
    rw [ite_eq_right (by simp), bdEdge_mk]
    constructor
    · intro _ h
      have := congrFun h 1
      simp at this
    · intro _
      funext i
      fin_cases i <;> simp

example : ∃ c : (faceBoundaryGraph ({![0, 0]} : Set (Site 2))).Walk ![0, 0] ![0, 0],
    c.IsCycle ∧ ![-1, 0] ∈ c.support :=
  djfx_faceBoundaryGraph_edgeCycle _ (Set.finite_singleton _) adj_single

example : (![1, 1] : Site 2) ∈ djfx_bowtie := djfx_mem_bowtie.mpr (Or.inr ⟨rfl, rfl⟩)

example : (![1, 0] : Site 2) ∉ djfx_bowtie := by
  rw [djfx_mem_bowtie]; simp

example : ¬ djfx_DiscreteJordanSeparation' := not_djfx_DiscreteJordanSeparation'

end MathlibExtTest.StatMech.Probability.Percolation.DiscreteJordanSeparationVariant
