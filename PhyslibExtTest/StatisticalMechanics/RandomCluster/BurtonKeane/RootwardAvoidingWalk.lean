/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootwardAvoidingWalk

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootwardAvoidingWalk`

* `bc42_avoidingWalk_iff_connected_removeSite` on the all-closed configuration: the trivial
  connection gives an avoiding walk;
* `bc42_removeSite_openSubgraph_le` applied;
* the chain labelling: `bc42_chainFar_consistent` and the concrete values of `bc42_chainFarLab` by
  `decide`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootwardAvoidingWalk

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

variable {d : ℕ}

-- A trivial connection after removing `y` is an avoiding walk.
example (x y : Site d) (hxy : x ≠ y) :
    ∃ p : (openSubgraph d (fun _ => false)).Walk x x, ∀ v ∈ p.support, v ≠ y :=
  (bc42_avoidingWalk_iff_connected_removeSite _ hxy).mpr (connected_refl _ x)

-- Removing a site only deletes open edges.
example (ω : ConfigSpace (Sym2 (Site d))) (y a b : Site d)
    (h : (openSubgraph d (removeSite y ω)).Adj a b) : (openSubgraph d ω).Adj a b :=
  bc42_removeSite_openSubgraph_le y ω h

-- The chain labelling: concrete values and its consistency statement.
example : bc42_chainFarLab 1 1 = 101 ∧ bc42_chainFarLab 0 0 = 100 ∧ bc42_chainFarLab 1 2 = 2 :=
  ⟨by decide, by decide, by decide⟩

-- The single-parent labelling on the chain is consistent.
example : ∃ (x₀ y₀ z₀ : Fin 3) (R : Fin 3 → Fin 3 → Fin 3 → Prop),
    (∀ c u v, R c u v ↔ bc42_chainFarLab c u = bc42_chainFarLab c v) ∧
    x₀ ≠ y₀ ∧ x₀ ≠ z₀ ∧ y₀ ≠ z₀ ∧ R 0 y₀ z₀ ∧ ¬ R 1 x₀ z₀ :=
  bc42_chainFar_consistent

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootwardAvoidingWalk
