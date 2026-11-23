/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Pressure

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Pressure`

* `Z` of a two-level system with energies `0` and `1`.
* `pressure` of the Ising model on the single edge `⊤ : SimpleGraph (Fin 2)` at zero field is
  `log (4 cosh β)`, through `ising_pressure_eq` and an explicit sum over the four configurations.
  (This `pressure` is the limit over independent copies of one finite system, not the lattice
  thermodynamic limit; see the module docstring.)
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Pressure

open _root_.StatMech _root_.StatMech.Ising

-- A two-level system with energies `0` and `1` has partition function `1 + e^{-β}`.
example (β : ℝ) : Z β (fun b : Bool => if b then (1 : ℝ) else 0) = Real.exp (-β) + 1 := by
  simp [Z]

/-- The single edge, the complete graph on two vertices. -/
abbrev edge : SimpleGraph (Fin 2) := ⊤

/-- A sum over the four configurations on two sites, written out. -/
lemma sum_config_two (f : ConfigSpace (Fin 2) → ℝ) :
    ∑ s, f s = f ![true, true] + f ![true, false] + f ![false, true] + f ![false, false] := by
  rw [← Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Bool)).symm f, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, piFinTwoEquiv_symm_apply]
  rw [← add_assoc]
  rfl

/-- The edge set of the single edge is `{s(0, 1)}`. -/
lemma edgeFinset_edge : edge.edgeFinset = {s(0, 1)} := by
  decide

-- The pressure of the single-edge Ising model at zero field is `log (4 cosh β)`.
example (β : ℝ) : pressure β (hamiltonian edge 0) = Real.log (4 * Real.cosh β) := by
  rw [ising_pressure_eq]
  congr 1
  rw [isingZ, sum_config_two]
  simp only [isingWeight, hamiltonian, edgeFinset_edge, Finset.sum_singleton, bond_mk]
  simp [spin, Real.cosh_eq]
  ring

end PhyslibExtTest.CondensedMatter.IsingModel.Pressure
