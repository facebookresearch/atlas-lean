/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExtremeCell
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExtremeCell`

* `exists_extremeCell` and `exists_convex_corner_dart` for the one-site set `{0}` and for the
  domino.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExtremeCell

example : ∃ c, IsExtremeCell ({0} : Set (Site 2)) c :=
  exists_extremeCell _ (Set.finite_singleton 0) (Set.singleton_nonempty 0)

example : ∃ e : Dart, IsBoundaryDart ({0} : Set (Site 2)) e ∧ turnZ {0} e = -1 :=
  exists_convex_corner_dart _ (Set.finite_singleton 0) (Set.singleton_nonempty 0)

example : ∃ e : Dart, IsBoundaryDart ({0, ![1, 0]} : Set (Site 2)) e ∧
    turnZ {0, ![1, 0]} e = -1 :=
  exists_convex_corner_dart _ (Set.toFinite _) (Set.insert_nonempty _ _)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExtremeCell
