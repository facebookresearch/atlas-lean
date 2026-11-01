/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanOuterFaceUnique

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanOuterFaceUnique`

Applies `regionGraph_unique_infinite_component` (a finite subgraph of `ℤ²` has exactly one
unbounded region) to the unit square `(0,0) - (1,0) - (1,1) - (0,1)`, and `outerRegion_infinite`
and `boundedRegion_iff_ne_outer` to the same graph: the outer region is infinite, so it is not
bounded.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanOuterFaceUnique

open _root_.StatMech _root_.StatMech.Lattice _root_.SimpleGraph

/-- The 4-cycle `0 - 1 - 2 - 3 - 0`. -/
def cyc4 : SimpleGraph (Fin 4) where
  Adj i j := ((j = i + 1) || (i = j + 1)) = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

/-- The corners of the unit square, in cyclic order. -/
def sqEmb : Fin 4 → Site 2 := ![![0, 0], ![1, 0], ![1, 1], ![0, 1]]

/-- The unit square of `ℤ²` as a planar subgraph. -/
def unitSquare : PlanarZ2Subgraph where
  V := Fin 4
  finV := inferInstance
  decV := inferInstance
  G := cyc4
  emb := ⟨sqEmb, by decide +kernel⟩
  isSub := by
    intro i j h
    change ((j = i + 1) || (i = j + 1)) = true at h
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    revert h; fin_cases i <;> fin_cases j <;> simp [sqEmb]

-- The unit square has exactly one unbounded region.
example : ∃! C : (regionGraph (imageGraph unitSquare)).ConnectedComponent, C.supp.Infinite :=
  regionGraph_unique_infinite_component unitSquare

-- The designated outer region of the unit square is infinite, hence not bounded.
example : ¬ (outerRegion unitSquare).supp.Finite := by
  rw [boundedRegion_iff_ne_outer]; exact fun h => h rfl

example : (outerRegion unitSquare).supp.Infinite := outerRegion_infinite unitSquare

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanOuterFaceUnique
