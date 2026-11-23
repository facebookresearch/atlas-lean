/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.DensityBounds

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.DensityBounds`

On the one-edge graph `⊤ : SimpleGraph (Fin 2)` at `p = 1/2`, `q = 2`:
* `edge_density_bounds` for `edgeMarginalOpen` (the probability that an edge is open):
  `p / (p + q(1 - p)) = 1/3 ≤ φ(edge {0, 1} open) ≤ p = 1/2`;
* `edge_density_finiteEnergy` applies to every coordinate.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.DensityBounds

open _root_.StatMech _root_.StatMech.FK

/-- The edge `{0, 1}` of `⊤ : SimpleGraph (Fin 2)`. -/
theorem mem_edgeFinset : s(0, 1) ∈ (⊤ : SimpleGraph (Fin 2)).edgeFinset := by simp

-- The density bounds at `p = 1/2`, `q = 2`: `1/3 ≤ φ(e open) ≤ 1/2`.
example : 1 / 3 ≤ edgeMarginalOpen (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 s(0, 1) ∧
    edgeMarginalOpen (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 s(0, 1) ≤ 1 / 2 := by
  have h := edge_density_bounds (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num)
    (by norm_num) (by norm_num) mem_edgeFinset
  norm_num at h ⊢
  exact h

-- The finite-energy bounds apply to every coordinate.
example (e : Sym2 (Fin 2)) :
    cFE (1 / 2) 2 ≤ edgeMarginalOpen (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 e ∧
      edgeMarginalOpen (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 e ≤ 1 - cFE (1 / 2) 2 :=
  edge_density_finiteEnergy _ (by norm_num) (by norm_num) (by norm_num) e

end PhyslibExtTest.StatisticalMechanics.RandomCluster.DensityBounds
