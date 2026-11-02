/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting`

In the plane:
* `connected_removeSite_forceOpen_of_corridor`: forcing the edge `(1,0)–(2,0)` connects its ends
  after removing the origin (all-closed configuration);
* `isOpenEdge_removeSite_forceOpen_step` on the same edge;
* `measurableSet_neighborTrifPrecursor` at the three axis neighbours;
* `hroute_of_corridorCover` in conditional form for a finite-energy probability measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Percolation.DisjointPaths MeasureTheory

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- `(1,0)` and `(2,0)` are lattice neighbours. -/
theorem adj10 : (hypercubicLattice 2).Adj ![1, 0] ![2, 0] := by
  simp [hypercubicLattice, NearestNeighbour, Fin.sum_univ_two]

/-- The edge `(1,0)–(2,0)` avoids the origin. -/
theorem notMem10 : (0 : Site 2) ∉ s(![1, 0], ![2, 0]) := by
  simp only [Sym2.mem_iff, not_or]
  constructor <;> intro h <;> simpa using congrFun h 0

-- Forcing the edge opens it after removing the origin.
example : IsOpenEdge 2 (removeSite 0 (forceOpenFinset {s(![1, 0], ![2, 0])} closed2))
    ![1, 0] ![2, 0] :=
  isOpenEdge_removeSite_forceOpen_step closed2 _ adj10 (Finset.mem_singleton_self _) notMem10

-- A one-step corridor connects its ends.
example : Connected 2 (removeSite 0 (forceOpenFinset {s(![1, 0], ![2, 0])} closed2))
    ![1, 0] ![2, 0] :=
  connected_removeSite_forceOpen_of_corridor closed2 _
    (Relation.ReflTransGen.single ⟨adj10, Finset.mem_singleton_self _, notMem10⟩)

-- Neighbour trifurcation precursors are measurable.
example : MeasurableSet (NeighborTrifPrecursor 2 ![1, 0] ![0, 1] ![-1, 0]) :=
  measurableSet_neighborTrifPrecursor _ _ _

-- A corridor cover at every scale gives positive-probability precursors.
example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (hcorr : ∀ n : ℕ, threeMeetBox 2 n ⊆
      ⋃ (a₁ : Site 2) (a₂ : Site 2) (a₃ : Site 2) (G : Finset (Sym2 (Site 2))),
        CorridorWorks a₁ a₂ a₃ G) (n : ℕ) (hpos : 0 < μ (threeMeetBox 2 n)) :
    ∃ a₁ a₂ a₃ : Site 2, 0 < μ (NeighborTrifPrecursor 2 a₁ a₂ a₃) :=
  hroute_of_corridorCover μ hfe hcorr n hpos

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting
