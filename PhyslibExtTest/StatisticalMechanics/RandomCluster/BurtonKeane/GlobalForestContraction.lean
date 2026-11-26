/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestContraction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestContraction`

* The second conjunct of `bc110_status` on the star graph with centre `0` and leaves `1, 2, 3`:
  the spanning forest keeps degree three at the centre (instance).
* The fourth conjunct gives `bc61_coarseTcount ≤ |∂B_R|` from `bc69_Gn_globalForest`, and the
  first one produces that forest from `bc103_ContractedTrifGraph` (conditional forms).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestContraction

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The star graph on `Fin 4` with centre `0`. -/
def star : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun a b => a = 0 ∧ b ≠ 0

/-- Deleting the centre leaves the star with no edges. -/
theorem star_delete : star.deleteIncidenceSet 0 = ⊥ := by
  ext a b
  simp only [SimpleGraph.deleteIncidenceSet_adj, star, SimpleGraph.fromRel_adj,
    SimpleGraph.bot_adj, iff_false]
  tauto

/-- Distinct leaves are not reachable once the centre is deleted. -/
theorem star_not_reach {a b : Fin 4} (h : a ≠ b) : ¬ (star.deleteIncidenceSet 0).Reachable a b := by
  rw [star_delete, SimpleGraph.reachable_bot]; exact h

-- The spanning forest of the star keeps degree three at its centre.
example [DecidableRel (osf_spanForest star).Adj] : 3 ≤ (osf_spanForest star).degree 0 :=
  (bc110_status (d := 1)).2.1 star 0 1 2 3 (by simp [star]) (by simp [star]) (by simp [star])
    (star_not_reach (by decide)) (star_not_reach (by decide)) (star_not_reach (by decide))

-- A contracted trifurcation graph gives the coarse counting bound.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (h : bc103_ContractedTrifGraph ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  (bc110_status (d := 2)).2.2.2 ω L R ((bc110_status (d := 2)).1 ω L R h)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestContraction
