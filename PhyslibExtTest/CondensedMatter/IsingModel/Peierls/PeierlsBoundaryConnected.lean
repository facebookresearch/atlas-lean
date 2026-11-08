/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsBoundaryConnected

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsBoundaryConnected`

* `boxCluster`: membership of `(1, 2)` and non-membership of `(2, 0)` and `(0, -1)` in
  `[0, 1] × [0, 2]`; the rectangle is a connected cluster (`boxCluster_isConnectedCluster`);
* `FaceBoundaryConnected` holds for the singleton `{0}` on its four faces and for the rectangles
  `[0, 1] × [0, 2]` and `[0, 4] × [0, 0]` on their frames;
* `boxCluster_single_dualCircuit` and `singletonOrigin_single_dualCircuit`: one closed dual trail
  through every contour edge.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Peierls.PeierlsBoundaryConnected

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Ising

-- The corner `(1, 2)` lies in the rectangle `[0, 1] × [0, 2]`.
example : (![1, 2] : Site 2) ∈ boxCluster 1 2 := by
  rw [mem_boxCluster]; simp

-- The site `(2, 0)` does not.
example : (![2, 0] : Site 2) ∉ boxCluster 1 2 := by
  rw [mem_boxCluster]; simp

-- The site `(0, -1)` does not.
example : (![0, -1] : Site 2) ∉ boxCluster 1 2 := by
  rw [mem_boxCluster]; simp

-- The rectangle is a connected cluster containing the origin.
example : IsConnectedCluster (boxCluster 1 2) := boxCluster_isConnectedCluster 1 2

-- The contour of the singleton `{0}` is connected on its four faces.
example : FaceBoundaryConnected (↑({origin 2} : Finset (Site 2)) : Set (Site 2))
    singletonBoundarySupport :=
  singletonOrigin_faceBoundaryConnected

-- The contour of `[0, 1] × [0, 2]` is connected on its frame.
example : FaceBoundaryConnected (↑(boxCluster 1 2) : Set (Site 2)) (boxFrame 1 2) :=
  boxCluster_faceBoundaryConnected 1 2

-- The contour of the segment `[0, 4] × [0, 0]` is connected on its frame.
example : FaceBoundaryConnected (↑(boxCluster 4 0) : Set (Site 2)) (boxFrame 4 0) :=
  boxCluster_faceBoundaryConnected 4 0

-- One closed dual trail covers the contour of `[0, 1] × [0, 2]`.
example : ∃ c : (faceBoundaryGraph (↑(boxCluster 1 2) : Set (Site 2))).Walk
      ![(-1 : ℤ), -1] ![(-1 : ℤ), -1],
    c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑(boxCluster 1 2) : Set (Site 2))).edgeSet,
      e ∈ c.edges :=
  boxCluster_single_dualCircuit 1 2

-- One closed dual trail covers the contour of the singleton.
example : ∃ c : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk
      ![(0 : ℤ), 0] ![(0 : ℤ), 0],
    c.IsTrail ∧
      ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet,
        e ∈ c.edges :=
  singletonOrigin_single_dualCircuit

end PhyslibExtTest.CondensedMatter.IsingModel.Peierls.PeierlsBoundaryConnected
