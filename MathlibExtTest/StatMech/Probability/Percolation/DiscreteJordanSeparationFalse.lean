/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.DiscreteJordanSeparationFalse

/-!
# Tests for `MathlibExt.Probability.Percolation.DiscreteJordanSeparationFalse`

* The face-boundary graph of `∅` has no edges (`djsf_faceBoundaryGraph_empty_not_adj`) at
  concrete faces, and no edge is a boundary edge of `∅`.
* `djsf_djs_is_false` is restated.
-/

@[expose] public section

open StatMech.Lattice StatMech.Percolation

namespace MathlibExtTest.StatMech.Probability.Percolation.DiscreteJordanSeparationFalse

example : ¬ (faceBoundaryGraph (∅ : Set (Site 2))).Adj ![0, 0] ![1, 0] :=
  djsf_faceBoundaryGraph_empty_not_adj _ _

example : ¬ bdEdge (∅ : Set (Site 2)) s(![0, 0], ![0, 1]) := djsf_not_bdEdge_empty _

example : ¬ DiscreteJordanSeparation := djsf_djs_is_false

end MathlibExtTest.StatMech.Probability.Percolation.DiscreteJordanSeparationFalse
