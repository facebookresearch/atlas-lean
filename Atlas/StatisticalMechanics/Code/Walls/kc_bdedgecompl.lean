/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.Lattice.JordanEnclosure
import Code.Lattice.FaceRegion

open Finset Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice







section Node

variable (S : Set (Site 2))










theorem bdEdge_compl (e : Sym2 (Site 2)) : bdEdge S e ↔ bdEdge Sᶜ e := by
  refine Sym2.recOnSubsingleton e (fun x y => ?_)
  rw [bdEdge_mk, bdEdge_mk]
  simp only [Set.mem_compl_iff]
  tauto




theorem bdEdge_compl_mk (x y : Site 2) :
    bdEdge S s(x, y) ↔ bdEdge Sᶜ s(x, y) :=
  bdEdge_compl S s(x, y)



theorem bdEdge_compl_mk_iff (x y : Site 2) :
    bdEdge Sᶜ s(x, y) ↔ (x ∉ S ↔ y ∈ S) := by
  rw [bdEdge_mk]
  simp only [Set.mem_compl_iff]
  tauto

end Node







section SetForm

variable (S : Set (Site 2))





theorem bdEdgeSet2_compl : bdEdgeSet2 S = bdEdgeSet2 Sᶜ := by
  apply Set.ext
  intro e
  refine Sym2.recOnSubsingleton e (fun x y => ?_)
  rw [mem_bdEdgeSet2, mem_bdEdgeSet2]
  simp only [Set.mem_compl_iff]
  tauto




theorem faceBoundaryGraph_compl : faceBoundaryGraph S = faceBoundaryGraph Sᶜ := by
  apply SimpleGraph.ext
  ext f g
  rw [faceBoundaryGraph_adj, faceBoundaryGraph_adj]
  rw [bdEdge_compl S (sharedPrimalEdge f g)]

end SetForm









section MatchBlind

variable {K T : Set (Site 2)}




theorem bdEdge_match_compl_left (hmatch : ∀ e : Sym2 (Site 2), bdEdge K e ↔ bdEdge T e) :
    ∀ e : Sym2 (Site 2), bdEdge Kᶜ e ↔ bdEdge T e := by
  intro e
  rw [← bdEdge_compl K e]
  exact hmatch e






theorem bdEdge_match_compl_right (hmatch : ∀ e : Sym2 (Site 2), bdEdge K e ↔ bdEdge T e) :
    ∀ e : Sym2 (Site 2), bdEdge K e ↔ bdEdge Tᶜ e := by
  intro e
  rw [← bdEdge_compl T e]
  exact hmatch e



theorem bdEdge_match_compl_both :
    (∀ e : Sym2 (Site 2), bdEdge K e ↔ bdEdge T e) ↔
      (∀ e : Sym2 (Site 2), bdEdge Kᶜ e ↔ bdEdge Tᶜ e) := by
  constructor
  · intro hmatch e
    rw [← bdEdge_compl K e, ← bdEdge_compl T e]
    exact hmatch e
  · intro hmatch e
    rw [bdEdge_compl K e, bdEdge_compl T e]
    exact hmatch e

end MatchBlind

end Walls

end StatMech
