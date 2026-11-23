/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsSingleCircuit

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsSingleCircuit`

* Euler's theorem `EulerianExistence.exists_closed_eulerian` (and its Mathlib form
  `exists_closed_isEulerian`) on the complete graph `K₅`, where every degree is `4`, at base
  vertex `2`; the circuit has length `10 = |E(K₅)|` (`exists_closed_eulerian_length`);
* `FaceBoundaryConnected` is not trivially true: it fails for the empty face set.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Peierls.PeierlsSingleCircuit

open _root_.StatMech _root_.StatMech.Lattice

/-- Every vertex of `K₅` has even degree `4`. -/
lemma k5_even_degree (v : Fin 5) : Even ((⊤ : SimpleGraph (Fin 5)).degree v) := by
  rw [SimpleGraph.complete_graph_degree]
  decide

-- Euler's theorem on `K₅`: a closed trail at vertex `2` through every edge.
example : ∃ p : (⊤ : SimpleGraph (Fin 5)).Walk 2 2,
    p.IsTrail ∧ ∀ e ∈ (⊤ : SimpleGraph (Fin 5)).edgeFinset, e ∈ p.edges :=
  EulerianExistence.exists_closed_eulerian _ SimpleGraph.connected_top k5_even_degree 2

-- The same circuit as a Mathlib Eulerian walk.
example : ∃ p : (⊤ : SimpleGraph (Fin 5)).Walk 2 2, p.IsEulerian :=
  EulerianExistence.exists_closed_isEulerian _ SimpleGraph.connected_top k5_even_degree 2

-- The Euler circuit of `K₅` has length `10`.
example : ∃ p : (⊤ : SimpleGraph (Fin 5)).Walk 0 0, p.IsTrail ∧ p.length = 10 := by
  obtain ⟨p, hp, -, hlen⟩ :=
    EulerianExistence.exists_closed_eulerian_length _ SimpleGraph.connected_top k5_even_degree 0
  exact ⟨p, hp, by rw [hlen]; decide⟩

-- `FaceBoundaryConnected` fails on the empty face set (a connected graph is nonempty).
example (K : Set (Site 2)) : ¬ FaceBoundaryConnected K ∅ := by
  intro h
  obtain ⟨⟨v, hv⟩⟩ := h.nonempty
  simp at hv

end PhyslibExtTest.CondensedMatter.IsingModel.Peierls.PeierlsSingleCircuit
