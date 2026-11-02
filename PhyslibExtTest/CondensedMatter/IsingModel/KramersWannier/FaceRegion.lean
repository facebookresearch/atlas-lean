/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.FaceRegion

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.KramersWannier.FaceRegion`

* `fwr_primalWalkBoundsRegion_false` refutes `PrimalWalkBoundsRegion`, and hence (with
  `kwc_primalWalkBoundsRegion_of_leftRegionMatch`) `kwc_PrimalWalkLeftRegionMatch`;
* `fwr_faceCutFlip` and `fwr_faceCutMatch_nil` on the adjacent faces `(0, 1)` and `(1, 1)`;
* `fwr_primalWalkBoundsFaceRegion` holds unconditionally.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.FaceRegion

open _root_.StatMech _root_.StatMech.Walls _root_.StatMech.Lattice

-- The site-region form is false.
example : ¬ PrimalWalkBoundsRegion := fwr_primalWalkBoundsRegion_false

-- So is the stronger inside-region matching.
example : ¬ kwc_PrimalWalkLeftRegionMatch := fun h =>
  fwr_primalWalkBoundsRegion_false (kwc_primalWalkBoundsRegion_of_leftRegionMatch h)

-- The face-region parity flip for the shifted unit-square loop and two adjacent faces.
example : (fwr_faceInside ceo_shiftSquare ![0, 1] ↔ ¬ fwr_faceInside ceo_shiftSquare ![1, 1]) ↔
    Odd (List.count (sharedPrimalEdge ![0, 1] ![1, 1]) ceo_shiftSquare.edges) :=
  fwr_faceCutFlip ceo_shiftSquare ceo_uv_adj

-- For the empty walk, adjacent faces never separate along a traversed edge.
example : (fwr_faceInside (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk (0 : Site 2) 0)
      ![0, 1] ↔
    ¬ fwr_faceInside (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk (0 : Site 2) 0) ![1, 1]) ↔
      sharedPrimalEdge ![0, 1] ![1, 1] ∈
        (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk (0 : Site 2) 0).edges :=
  fwr_faceCutMatch_nil ceo_uv_adj

-- The face-region form holds.
example : fwr_PrimalWalkBoundsFaceRegion := fwr_primalWalkBoundsFaceRegion

end PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.FaceRegion
