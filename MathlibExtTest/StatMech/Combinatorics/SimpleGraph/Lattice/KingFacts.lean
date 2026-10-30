/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingFacts
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingFacts`

* `kf_hyperAdj_kingAdj` on the edge from the origin to `(1, 0)`; `KingAdj` for the diagonal step.
* `kf_boundaryKingConnected` for an arbitrary set.
* `kf_interfaceConnected_of_orbitResidues` for `K = ∅` (its transport hypothesis is false for
  every finite nonempty `K`, see `ifg_not_orbitKingTransport_of_finite`).
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingFacts

example : KingAdj (0 : Site 2) ![1, 0] :=
  kf_hyperAdj_kingAdj _ _ (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)

example : KingAdj (0 : Site 2) ![1, 1] := ⟨by
    intro h; have := congrFun h 0; simp at this, fun i => by fin_cases i <;> simp⟩

example (K : Set (Site 2)) : BoundaryKingConnected K := kf_boundaryKingConnected K

example : InterfaceConnected (∅ : Set (Site 2)) :=
  kf_interfaceConnected_of_orbitResidues ∅ (fun e he => absurd he.1 (by simp))
    (fun e he => absurd he.1 (by simp))

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingFacts
