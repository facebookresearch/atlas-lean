/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiberLeafBoundary

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiberLeafBoundary`

In the plane:
* `bc84_upperLines_coarseTrif_and_top` at `L = 3`;
* `bc84_upperLines_obstruction_is_cut` at `L = 3`: a `Gn` trifurcation with a disjoint buffer box;
* `bc84_peeling_forest_le_boundary` and the fibre-bound clause of `bc84_status` in conditional
  form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FiberLeafBoundary

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- The upper lines are a coarse trifurcation with `N = ⊤`.
example : bc61_IsCoarseTrifurcation bc60_upperLines 3 (0 : Site 2) ∧
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc84_upperLines_coarseTrif_and_top le_rfl

-- The `Gn` obstruction: the upper lines are a `Gn` trifurcation at `L = 3` with disjoint buffer.
example : bc67_IsGnTrifurcation bc60_upperLines 3 (0 : Site 2) ∧
    Disjoint (bc61_boxAround 2 3 (0 : Site 2)) (bc61_boxAround 2 3 (bc76_yBuf 3)) :=
  ⟨(bc84_upperLines_obstruction_is_cut le_rfl).1, (bc84_upperLines_obstruction_is_cut le_rfl).2.1⟩

-- The peeling bound for a forest whose leaves map injectively to the boundary.
example {W : Type} [Fintype W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] (R : ℕ)
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) (lam : W → Site 2)
    (hmap : ∀ v, G.degree v = 1 → lam v ∈ vertexBoundary 2 R)
    (hinj : Set.InjOn lam (Finset.univ.filter (fun v => G.degree v = 1))) :
    (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card ≤ boxSV_boundaryCard 2 R :=
  bc84_peeling_forest_le_boundary G R hacyc hmin lam hmap hinj

-- Fibre data give the fibre bound.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1))
    (h : bc75_FiberGnTrifData ω L R c) : (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard 2 R :=
  bc84_status.2.2.1 ω L R c h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FiberLeafBoundary
