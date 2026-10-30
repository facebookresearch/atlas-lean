/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullFinite

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullFinite`

* The star hull of a finite set is finite: instantiated at the unit cell and at the domino.
* The star hull lies in the box spanned by the coordinate projections.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.StarHullFinite

example : (ndt_StarHull unitCell).Finite := starHull_finite unitCell unitCell_finite

example : (ndt_StarHull domino).Finite := starHull_finite domino domino_finite

example : ndt_StarHull unitCell ⊆ {x : Site 2 | ∀ i, x i ∈ (fun y => y i) '' unitCell} :=
  shf_starHull_subset_projBox unitCell

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.StarHullFinite
