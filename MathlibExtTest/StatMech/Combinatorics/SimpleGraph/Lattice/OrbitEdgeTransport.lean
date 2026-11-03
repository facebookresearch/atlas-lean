/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitEdgeTransport
public import Mathlib.Tactic

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitEdgeTransport`

* `InterfaceConnected` for `K = ∅`, directly (there is no boundary dart of `∅`). The transport
  reduction `icb_interfaceConnected_of_unitEdgeTransport` was removed: its hypothesis fails for
  every finite nonempty `K` (`icb_not_unitEdgeTransport_of_finite`, tested on `{0, (0, 1)}`).
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitEdgeTransport

example : InterfaceConnected (∅ : Set (Site 2)) := by
  intro e f he hf hreach
  exact absurd he.1 (by simp)

example : ¬ UnitEdgeOrbitTransport ({0, ![0, 1]} : Set (Site 2)) :=
  icb_not_unitEdgeTransport_of_finite _ (Set.toFinite _) (Set.insert_nonempty _ _)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitEdgeTransport
