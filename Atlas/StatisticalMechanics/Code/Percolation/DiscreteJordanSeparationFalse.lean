/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































import Mathlib
import Code.Percolation.ClusterDualContour
import Code.Lattice.JordanEnclosure

open Set SimpleGraph

namespace StatMech

namespace Percolation

open StatMech.Lattice


theorem djsf_not_bdEdge_empty (e : Sym2 (Site 2)) : ¬ bdEdge (∅ : Set (Site 2)) e := by
  induction e using Sym2.ind with
  | _ x y => rw [bdEdge_mk]; simp


theorem djsf_faceBoundaryGraph_empty_not_adj (f g : Site 2) :
    ¬ (faceBoundaryGraph (∅ : Set (Site 2))).Adj f g := by
  rw [faceBoundaryGraph_adj]
  rintro ⟨-, hbd⟩
  exact djsf_not_bdEdge_empty _ hbd





theorem djsf_djs_is_false : ¬ DiscreteJordanSeparation := by
  intro h
  obtain ⟨c, hcyc, _⟩ := h (∅ : Set (Site 2)) Set.finite_empty (Reachable.refl (origin 2))
  obtain ⟨g, e, rest, rfl⟩ := (Walk.not_nil_iff).mp hcyc.not_nil
  rw [faceBoundaryGraph_adj] at e
  exact djsf_not_bdEdge_empty _ e.2

end Percolation

end StatMech
