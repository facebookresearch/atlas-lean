/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.KWSelfDuality

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.KWSelfDuality`

* `IsEvenSubgraph`: on the single edge `⊤ : SimpleGraph (Fin 2)` the empty edge set is even and
  the edge itself is not (both endpoints have degree one).
* `isingZ_high_temp_expansion` on the single edge: the only even subgraph is `∅`, so the expansion
  gives `Z(β) = 4 cosh β`; the same value is computed directly from the four configurations, so the
  expansion is checked against the definition of `isingZ`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.KWSelfDuality

open _root_.StatMech _root_.StatMech.Ising

/-- The single edge, the complete graph on two vertices. -/
abbrev edge : SimpleGraph (Fin 2) := ⊤

/-- The edge set of the single edge is `{s(0, 1)}`. -/
lemma edgeFinset_edge : edge.edgeFinset = {s(0, 1)} := by
  decide

/-- A sum over the four configurations on two sites, written out. -/
lemma sum_config_two (f : ConfigSpace (Fin 2) → ℝ) :
    ∑ s, f s = f ![true, true] + f ![true, false] + f ![false, true] + f ![false, false] := by
  rw [← Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Bool)).symm f, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, piFinTwoEquiv_symm_apply]
  rw [← add_assoc]
  rfl

-- The empty edge set is an even subgraph.
example : IsEvenSubgraph (∅ : Finset (Sym2 (Fin 2))) := by decide

-- A single edge is not an even subgraph: its endpoints have odd degree.
example : ¬ IsEvenSubgraph ({s(0, 1)} : Finset (Sym2 (Fin 2))) := by decide

/-- The even subgraphs of the single edge: only `∅`. -/
lemma evenSubgraphs_edge :
    edge.edgeFinset.powerset.filter IsEvenSubgraph = {∅} := by
  rw [edgeFinset_edge]
  decide

-- The high-temperature expansion on the single edge: `Z(β) = 4 cosh β`.
example (β : ℝ) : isingZ edge β 0 = 4 * Real.cosh β := by
  rw [isingZ_high_temp_expansion, evenSubgraphs_edge, edgeFinset_edge]
  simp
  norm_num

-- The same value from the definition of `isingZ`, summing the four Boltzmann weights.
example (β : ℝ) : isingZ edge β 0 = 4 * Real.cosh β := by
  rw [isingZ, sum_config_two]
  simp only [isingWeight, hamiltonian, edgeFinset_edge, Finset.sum_singleton, bond_mk]
  simp [spin, Real.cosh_eq]
  ring

end PhyslibExtTest.CondensedMatter.IsingModel.KWSelfDuality
