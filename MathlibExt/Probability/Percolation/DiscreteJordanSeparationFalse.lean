/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.DiscreteJordanSeparation
public import MathlibExt.Probability.Percolation.Theta

/-!
# The discrete Jordan separation property is false

The face-boundary graph of `∅` has no edges, so the origin face is reachable from itself but lies on
no cycle. This refutes `StatMech.Percolation.DiscreteJordanSeparation`.

## Main results

* `StatMech.Percolation.djsf_djs_is_false`: `¬ DiscreteJordanSeparation`.
-/

@[expose] public section

open Set SimpleGraph

namespace StatMech

namespace Percolation

open StatMech.Lattice

/-- No edge is a boundary edge of `∅`. -/
theorem djsf_not_bdEdge_empty (e : Sym2 (Site 2)) : ¬ bdEdge (∅ : Set (Site 2)) e := by
  induction e using Sym2.ind with
  | _ x y => rw [bdEdge_mk]; simp

/-- The face-boundary graph of `∅` has no edges. -/
theorem djsf_faceBoundaryGraph_empty_not_adj (f g : Site 2) :
    ¬ (faceBoundaryGraph (∅ : Set (Site 2))).Adj f g := by
  rw [faceBoundaryGraph_adj]
  rintro ⟨-, hbd⟩
  exact djsf_not_bdEdge_empty _ hbd

/-- `DiscreteJordanSeparation` is false: for `K = ∅` and `a = b` the origin face, there is no
cycle at all. The failure is degenerate (an isolated face); the corrected variant
`djfx_DiscreteJordanSeparation'` excludes it but is false for other reasons
(`not_djfx_DiscreteJordanSeparation'`). -/
theorem djsf_djs_is_false : ¬ DiscreteJordanSeparation := by
  intro h
  obtain ⟨c, hcyc, _⟩ := h (∅ : Set (Site 2)) Set.finite_empty (Reachable.refl (origin 2))
  obtain ⟨g, e, rest, rfl⟩ := (Walk.not_nil_iff).mp hcyc.not_nil
  rw [faceBoundaryGraph_adj] at e
  exact djsf_not_bdEdge_empty _ e.2

end Percolation

end StatMech
