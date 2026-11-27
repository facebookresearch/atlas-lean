/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HarmBoxCoarseReach

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HarmBoxCoarseReach`

* The second conjunct of `bc107_status`: an open edge from a site of `B_{n-1}` stays in `B_n`;
  applied to the one-edge configuration `{(0, 0), (1, 0)}` of `ℤ²` (instance).
* `bc107_three_arms_reach_boundary` as a conditional statement.
* The first conjunct: an infinite coarse arm in the box reaches the boundary (conditional form).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.HarmBoxCoarseReach

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The configuration of `ℤ²` whose only open edge is `{(0, 0), (1, 0)}`. -/
noncomputable def ω₁ : ConfigSpace (Sym2 (Site 2)) := fun e => decide (e = s(0, ![1, 0]))

-- The open neighbour `(1, 0)` of the origin lies in `B_1`.
example : (![1, 0] : Site 2) ∈ box 2 1 :=
  (bc107_status (d := 2) (by norm_num)).2.1 ω₁ 1 le_rfl (x := 0) (fun i => by simp)
    (by simp [ω₁, Fin.sum_univ_two])

-- The three arms of a coarse trifurcation reach the boundary.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (hR : 1 ≤ R) (y : Site 2)
    (h : bc61_IsCoarseTrifurcation ω L y) {a₁ a₂ a₃ : Site 2}
    (hbox : a₁ ∈ box 2 R ∧ a₂ ∈ box 2 R ∧ a₃ ∈ box 2 R)
    (harm : (cluster 2 (removeSites (bc61_boxAround 2 L y) ω) a₁).Infinite ∧
      (cluster 2 (removeSites (bc61_boxAround 2 L y) ω) a₂).Infinite ∧
      (cluster 2 (removeSites (bc61_boxAround 2 L y) ω) a₃).Infinite) :
    (∃ z ∈ vertexBoundary 2 R, (bc67_contractedLattice ω L y).Reachable a₁ z) ∧
    (∃ z ∈ vertexBoundary 2 R, (bc67_contractedLattice ω L y).Reachable a₂ z) ∧
    (∃ z ∈ vertexBoundary 2 R, (bc67_contractedLattice ω L y).Reachable a₃ z) :=
  bc107_three_arms_reach_boundary ω L R hR y h hbox harm

-- One infinite arm reaches the boundary.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (hR : 1 ≤ R) (y a : Site 2)
    (ha : a ∈ box 2 R) (hinf : (cluster 2 (removeSites (bc61_boxAround 2 L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary 2 R, (bc67_contractedLattice ω L y).Reachable a z :=
  (bc107_status (d := 2) (by norm_num)).1 ω L R hR y a ha hinf

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.HarmBoxCoarseReach
