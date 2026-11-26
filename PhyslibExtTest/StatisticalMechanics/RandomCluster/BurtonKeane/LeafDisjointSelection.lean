/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LeafDisjointSelection

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LeafDisjointSelection`

* `tffa_count_unsat`: no injection from the eight leaf slots `Option (Fin 4 × Fin 2)` (nine
  values) into `Fin 6` (instance of the counting obstruction).
* In the all-closed configuration of `ℤ` the leaf selection `tffa_LeafDisjointSelection` holds
  (non-vacuity).
* `tffa_leafDisjoint_of_twoFoldForestArms` and `tffa_claw_excludes_twoFoldForestArms` as
  conditional statements.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.LeafDisjointSelection

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

-- The counting obstruction.
example : ¬ ∃ f : Option (Fin 4 × Fin 2) → Fin 6, Function.Injective f :=
  fun ⟨f, hf⟩ => tffa_count_unsat f hf

/-- In the all-closed configuration every cluster is a single site, so no site is a
trifurcation. -/
theorem not_isTrifurcation_closed {d : ℕ} (x : Site d) :
    ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a, -, -, -, -, ⟨h, -, -⟩, -⟩
  have hb : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
  have hc : cluster d (fun _ => false) a = {a} := by
    ext y
    simp [cluster, Connected, hb, eq_comm]
  exact h (hc ▸ Set.finite_singleton a)

/-- The site `1` of `ℤ` lies on the boundary of `B_1`. -/
theorem one_mem_vertexBoundary : (fun _ => 1 : Site 1) ∈ vertexBoundary 1 1 :=
  ⟨fun _ => le_rfl, fun h => by simpa using h 0⟩

-- A leaf-disjoint selection in the all-closed configuration.
example : tffa_LeafDisjointSelection (d := 1) (fun _ => false) 1 :=
  ⟨fun _ => 1, fun _ _ => 0, one_mem_vertexBoundary,
    fun x _ hx => absurd hx (not_isTrifurcation_closed x),
    fun x _ hx => absurd hx (not_isTrifurcation_closed x),
    fun x _ hx => absurd hx (not_isTrifurcation_closed x),
    fun x _ hx => absurd hx (not_isTrifurcation_closed x)⟩

-- Two-fold forest arms give a leaf selection.
example (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) (hn : 1 ≤ n) (h : tfh_TwoFoldForestArms ω n) :
    tffa_LeafDisjointSelection ω n :=
  tffa_leafDisjoint_of_twoFoldForestArms ω n hn h

-- A two-fold claw configuration excludes two-fold forest arms.
example (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) (hc : tffa_TwoFoldClawConfig ω n) :
    ¬ tfh_TwoFoldForestArms ω n :=
  tffa_claw_excludes_twoFoldForestArms ω n hc

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.LeafDisjointSelection
