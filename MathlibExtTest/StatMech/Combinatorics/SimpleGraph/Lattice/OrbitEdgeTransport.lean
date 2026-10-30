/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitEdgeTransport
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitEdgeTransport`

* `icb_interfaceConnected_of_unitEdgeTransport` for `K = ∅`, where both hypotheses hold vacuously
  (they fail for every finite nonempty `K`: `icb_not_unitEdgeTransport_of_finite`, tested on
  `{0, (0, 1)}`).
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitEdgeTransport

example : InterfaceConnected (∅ : Set (Site 2)) :=
  icb_interfaceConnected_of_unitEdgeTransport ∅ (fun e he => absurd he.1 (by simp))
    (fun e he => absurd he.1 (by simp))

example : ¬ UnitEdgeOrbitTransport ({0, ![0, 1]} : Set (Site 2)) :=
  icb_not_unitEdgeTransport_of_finite _ (Set.toFinite _) (Set.insert_nonempty _ _)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitEdgeTransport
