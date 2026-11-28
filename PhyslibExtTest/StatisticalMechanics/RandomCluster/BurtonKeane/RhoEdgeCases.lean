/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RhoEdgeCases

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RhoEdgeCases`

* instance: in `ℤ²`, forcing the edge `{(1, 0), (1, 1)}` open in the all-closed configuration and
  removing the origin leaves that edge open; `bc3_rho_endpoints_ne_zero` and
  `bc3_isOpenEdge_rho_cases` then classify it;
* `bc3_rho_omegaOpen_or_forced` on the all-closed configuration: every open edge is forced;
* `bc3_rho_openSubgraph_le_lattice` applied.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RhoEdgeCases

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The two boundary sites `(1, 0)` and `(1, 1)` of `B_1` in `ℤ²`. -/
def b₁ : Site 2 := ![1, 0]

/-- See `b₁`. -/
def b₂ : Site 2 := ![1, 1]

/-- `b₁` lies on the boundary of `B_1`. -/
theorem b₁_mem : b₁ ∈ vertexBoundary 2 1 := by
  simp only [mem_vertexBoundary, mem_box, b₁, Fin.forall_fin_two]
  decide

/-- `b₂` lies on the boundary of `B_1`. -/
theorem b₂_mem : b₂ ∈ vertexBoundary 2 1 := by
  simp only [mem_vertexBoundary, mem_box, b₂, Fin.forall_fin_two]
  decide

/-- The two boundary sites differ. -/
theorem b₁_ne_b₂ : b₁ ≠ b₂ := fun h => by simpa [b₁, b₂] using congrFun h 1
/-- The forced edge. -/
def G₀ : Finset (Sym2 (Site 2)) := {s(b₁, b₂)}

/-- The forced edge is open after forcing and removing the origin. -/
theorem rho_open : removeSite 0 (forceOpenFinset G₀ (fun _ => false)) s(b₁, b₂) = true := by
  have h1 : (0 : Site 2) ≠ b₁ := fun h => by simpa [b₁] using congrFun h 0
  have h2 : (0 : Site 2) ≠ b₂ := fun h => by simpa [b₂] using congrFun h 0
  simp [removeSite, forceOpenFinset, G₀, h1, h2]

-- Its endpoints avoid the origin.
example : b₁ ≠ 0 ∧ b₂ ≠ 0 := bc3_rho_endpoints_ne_zero _ G₀ rho_open

-- The case split for the open edge `{b₁, b₂}`: it is forced, not open in `ω`.
example : (hypercubicLattice 2).Adj b₁ b₂ ∧ (0 : Site 2) ∉ s(b₁, b₂) ∧
    ((fun _ => false) s(b₁, b₂) = true ∨ s(b₁, b₂) ∈ G₀) := by
  refine bc3_isOpenEdge_rho_cases _ G₀ ⟨?_, rho_open⟩
  simp [hypercubicLattice_adj, Fin.sum_univ_two, b₁, b₂]

-- In the all-closed configuration every open edge after the operation is forced.
example (G : Finset (Sym2 (Site 2))) (e : Sym2 (Site 2))
    (h : removeSite 0 (forceOpenFinset G (fun _ => false)) e = true) : e ∈ G :=
  (bc3_rho_omegaOpen_or_forced _ G h).resolve_left Bool.false_ne_true

-- The open subgraph after the operation is a lattice subgraph.
example (ω : ConfigSpace (Sym2 (Site 2))) (G : Finset (Sym2 (Site 2))) :
    openSubgraph 2 (removeSite 0 (forceOpenFinset G ω)) ≤ hypercubicLattice 2 :=
  bc3_rho_openSubgraph_le_lattice ω G

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RhoEdgeCases
