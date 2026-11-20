/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Walls.bmfmergefree

open Set SimpleGraph Finset MeasureTheory
open scoped ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech.Walls

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false




theorem bind_corridor_mem_I : s(bmf_a₁, bmf_b₁) ∈ bmf_I := by
  simp [bmf_I]



theorem bind_removeSite_corridor_eq (ω : ConfigSpace (Sym2 (Site 2))) :
    removeSite 0 ω s(bmf_a₁, bmf_b₁) = ω s(bmf_a₁, bmf_b₁) :=
  removeSite_apply_of_notMem bmf_o_notMem_e₁ ω




theorem bind_corridor_openEdge_iff_I (ω : ConfigSpace (Sym2 (Site 2))) :
    IsOpenEdge 2 (removeSite 0 ω) bmf_a₁ bmf_b₁ ↔ ω s(bmf_a₁, bmf_b₁) = true := by
  unfold IsOpenEdge
  rw [bind_removeSite_corridor_eq]
  exact ⟨fun h => h.2, fun h => ⟨bmf_adj_a₁_b₁, h⟩⟩


theorem bind_b₁_mem_corridor : bmf_b₁ ∈ s(bmf_a₁, bmf_b₁) := by
  simp







theorem bind_a₁_mem_cluster_b₁_of_I_open (ω : ConfigSpace (Sym2 (Site 2)))
    (h : ω s(bmf_a₁, bmf_b₁) = true) :
    bmf_a₁ ∈ cluster 2 (removeSite 0 ω) bmf_b₁ := by
  rw [mem_cluster]
  exact (IsOpenEdge.connected ((bind_corridor_openEdge_iff_I ω).mpr h)).symm

end StatMech.Walls
