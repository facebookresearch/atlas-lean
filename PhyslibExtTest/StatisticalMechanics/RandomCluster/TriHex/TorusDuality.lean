/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TorusDuality

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TorusDuality`

* `triangularTorusStep 5 2 = (4, 1)` (the step `(-1, 1)` reduced mod `5`);
* `(0, 0) ~ (1, 0)` on the triangular torus of side `3`;
* `triHexTorus_edge_card`: the two tori of side `3` have equally many edges;
* `triHexTorus_euler` for the empty subgraph of the side-`3` torus;
* `triHexTorus_fkWeight_duality` at `L = 3`, `p = 1 / 2`, `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TorusDuality

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.FK.PeriodicPlanar

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- The third triangular step on the torus of side `5`.
example : triangularTorusStep 5 2 = (4, 1) := by
  decide

-- A concrete edge of the triangular torus.
example : (triangularTorusGraph 3).Adj (0, 0) (1, 0) :=
  ⟨((0, 0), 0), by simp [triangularTorusIndexedEdge, triangularTorusStep]⟩

-- The edge duality matches edge counts.
example : (triangularTorusGraph 3).edgeFinset.card = (hexagonalTorusGraph 3).edgeFinset.card :=
  triHexTorus_edge_card 3

-- Euler's formula with defect for the empty subgraph.
example : (Nat.card (TorusSite 3) : ℤ) - (⊥ : SimpleGraph (TorusSite 3)).edgeSet.ncard +
      triHexTorusFaceCount 3 ⊥ =
    Nat.card (⊥ : SimpleGraph (TorusSite 3)).ConnectedComponent + 1 -
      triHexTorusEulerDefect 3 ⊥ :=
  triHexTorus_euler 3 ⊥

-- FK-weight duality on the side-`3` torus.
example (omega : ConfigSpace (Sym2 (TorusSite 3))) :=
  triHexTorus_fkWeight_duality 3 omega (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
    (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TorusDuality
