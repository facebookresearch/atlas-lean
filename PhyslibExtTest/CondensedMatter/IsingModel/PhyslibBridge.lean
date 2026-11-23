/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.PhyslibBridge

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.PhyslibBridge`

* `hamiltonian_eq_energy`: Physlib's Ising energy of the all-plus configuration on the single edge
  `⊤ : SimpleGraph (Fin 2)`, with `J = 1` and field `h`, is `-1 - 2h`, computed through the bridge.
* `isingZ_eq_mathematicalPartitionFunction`: Physlib's partition function of `canonicalEnsemble` at
  the temperature with `β = 0` is the number of configurations, `4`.
* `isingProb_eq_probability`: Physlib's canonical probabilities of the Ising ensemble are positive
  and sum to one, transported from `isingProb`; at `β = 0` they are uniform.
* `hypercubicLatticeIsoCrystal`: the image of an edge `{0, e₀}` of `ℤ²` is a bond of Physlib's
  hypercubic crystal graph, and a non-edge maps to a non-bond.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.PhyslibBridge

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Lattice

/-- The single edge, the complete graph on two vertices. -/
abbrev edge : SimpleGraph (Fin 2) := ⊤

/-- The edge set of the single edge is `{s(0, 1)}`. -/
lemma edgeFinset_edge : edge.edgeFinset = {s(0, 1)} := by
  decide

/-- The all-plus configuration on two sites. -/
def plus : ConfigSpace (Fin 2) := fun _ => true

open scoped Classical in
-- Physlib's Ising energy of the all-plus configuration, computed through the bridge.
example (h : ℝ) :
    (⟨1, h⟩ : CondensedMatter.IsingModel edge).energy Finset.univ plus = -1 - 2 * h := by
  rw [← hamiltonian_eq_energy, hamiltonian, edgeFinset_edge]
  simp [plus, spin]
  ring

-- Physlib's partition function at `β = 0` counts the four configurations.
example (h : ℝ) :
    (canonicalEnsemble edge h).mathematicalPartitionFunction (Temperature.ofβ 0) = 4 := by
  rw [← isingZ_eq_mathematicalPartitionFunction, Temperature.β_ofβ]
  simp [isingZ, isingWeight]

-- Physlib's canonical probability at `β = 0` is uniform.
example (h : ℝ) (s : ConfigSpace (Fin 2)) :
    (canonicalEnsemble edge h).probability (Temperature.ofβ 0) s = 1 / 4 := by
  rw [← isingProb_eq_probability, Temperature.β_ofβ]
  simp [isingProb, isingZ, isingWeight]

-- Physlib's canonical probabilities of the Ising ensemble are positive.
example (h : ℝ) (T : Temperature) (s : ConfigSpace (Fin 2)) :
    0 < (canonicalEnsemble edge h).probability T s := by
  rw [← isingProb_eq_probability]
  exact isingProb_pos edge _ h s

-- Physlib's canonical probabilities of the Ising ensemble sum to one.
example (h : ℝ) (T : Temperature) :
    ∑ s : ConfigSpace (Fin 2), (canonicalEnsemble edge h).probability T s = 1 := by
  simp_rw [← isingProb_eq_probability]
  exact isingProb_sum_eq_one edge _ h

-- An edge of `ℤ²` maps to a bond of Physlib's hypercubic crystal graph.
example : (CondensedMatter.Crystal.hypercubicGraph 2).toSimpleGraph.Adj
    (hypercubicLatticeIsoCrystal 2 0) (hypercubicLatticeIsoCrystal 2 (Pi.single 0 1)) := by
  rw [(hypercubicLatticeIsoCrystal 2).map_adj_iff, hypercubicLattice_adj]
  simp [Fin.sum_univ_two]

-- A diagonal pair of `ℤ²` is not a bond of the crystal graph.
example : ¬ (CondensedMatter.Crystal.hypercubicGraph 2).toSimpleGraph.Adj
    (hypercubicLatticeIsoCrystal 2 0) (hypercubicLatticeIsoCrystal 2 (fun _ => 1)) := by
  rw [(hypercubicLatticeIsoCrystal 2).map_adj_iff, hypercubicLattice_adj]
  simp

end PhyslibExtTest.CondensedMatter.IsingModel.PhyslibBridge
