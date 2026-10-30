/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingRevMatch
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingRevMatch`

* The refutation `owr_exists_not_exteriorHyp` for `K = {0}` and for the two-site set
  `{0, (1, 0)}`: the exterior hypothesis `hExt` fails for some boundary dart.
* `owr_revMatch_of_inclusions` with `K` equal to the even–odd inside of a closed walk.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitWindingRevMatch

example : ∃ (e : Dart) (he : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e),
    ¬ ∀ z, z ∉ ({(0 : Site 2)} : Set (Site 2)) → ∃ z0 : Site 2,
      ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (olb_orbitLoop _ (Set.finite_singleton _) e he).support) ∧
        (∀ q ∈ (olb_orbitLoop _ (Set.finite_singleton _) e he).support, z0 0 ≤ q 0) :=
  owr_exists_not_exteriorHyp _ _ (Set.singleton_nonempty _)

example : ∃ (e : Dart) (he : IsBoundaryDart ({0, ![1, 0]} : Set (Site 2)) e),
    ¬ ∀ z, z ∉ ({0, ![1, 0]} : Set (Site 2)) → ∃ z0 : Site 2,
      ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (olb_orbitLoop _ (Set.toFinite _) e he).support) ∧
        (∀ q ∈ (olb_orbitLoop _ (Set.toFinite _) e he).support, z0 0 ≤ q 0) :=
  owr_exists_not_exteriorHyp _ _ (Set.insert_nonempty _ _)

example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (x y : Site 2)
    (h : (hypercubicLattice 2).Adj x y) (hb : bdEdge (jec_leftRegion Vc) s(x, y)) :
    bdEdge (jec_leftRegion Vc) s(x, y) :=
  owr_revMatch_of_inclusions _ Vc le_rfl le_rfl x y h hb

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitWindingRevMatch
