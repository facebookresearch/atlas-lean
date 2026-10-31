/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryArmInjection

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryArmInjection`

* `lhc_boundaryArmInjection_of_uniqueTrif` for the all-closed configuration of `ℤ` with an
  explicit boundary site;
* `lhc_trace_card_le_boundary` for the all-open configuration;
* `lhc_clawTrace_card_consistent` at `T = 3`;
* `lhc_not_forall_boundaryArmInjection`: refuted for `d = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryArmInjection

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

/-- The all-closed configuration has no trifurcation. -/
theorem noTrif_closed {d : ℕ} (x : Site d) : ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a₁, a₂, -, ⟨h₁₂, -, -⟩, ⟨c₁, c₂, -⟩, -⟩
  have hbot : openSubgraph d (fun _ => false) = ⊥ := by
    ext u v; simp
  unfold Connected at c₁ c₂
  rw [hbot, SimpleGraph.reachable_bot] at c₁ c₂
  exact h₁₂ (c₁.symm.trans c₂)

/-- The site `1` lies on the vertex boundary of the box of radius `1` in `ℤ`. -/
theorem one_mem_boundary : (fun _ => 1 : Site 1) ∈ vertexBoundary 1 1 :=
  ⟨fun _ => le_rfl, fun h => absurd (h 0) (by decide)⟩

-- The boundary arm injection for the all-closed configuration.
example : tfc_BoundaryArmInjection (d := 1) (fun _ => false) 1 :=
  lhc_boundaryArmInjection_of_uniqueTrif _ 1 (r := 0) one_mem_boundary
    fun x _ hx => (noTrif_closed x hx).elim

-- The boundary trace is bounded by the boundary.
example (x₀ : Site 2) : (lhc_trace (fun _ => true) 2 x₀).card ≤ boxSV_boundaryCard 2 2 :=
  lhc_trace_card_le_boundary _ 2 x₀

-- The claw-trace card arithmetic at `T = 3`.
example : 3 + 2 < 2 * 3 := (lhc_clawTrace_card_consistent (T := 3) le_rfl).2

-- The boundary arm injection cannot hold for every configuration of `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → tfc_BoundaryArmInjection ω n :=
  lhc_not_forall_boundaryArmInjection le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryArmInjection
