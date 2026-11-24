/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.ErdosSimonovitsBalanced
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace MathlibExt.GraphTheory.ErdosProblem1077Wanted

example : disprovedMain := mainPositive_refuted

-- Adding an isolated vertex to a single edge precludes every finite balance factor.
example (D : ℝ) : ¬ (SimpleGraph.edge (0 : Fin 3) 1).IsBalanced D := by
  let G := SimpleGraph.edge (0 : Fin 3) 1
  have hmin : G.minDegree = 0 := SimpleGraph.minDegree_eq_zero_iff.mpr
    ⟨2, fun v hv ↦ by simp [G, SimpleGraph.edge_adj] at hv⟩
  have hadj : G.Adj 0 1 := by simp [G, SimpleGraph.edge_adj]
  change ¬ G.IsBalanced D
  intro hbal
  have hbot : G = ⊥ := by simpa [SimpleGraph.IsBalanced, hmin] using hbal
  simp [hbot] at hadj

-- The positive edge requirement matters: an edgeless graph can be balanced.
example (D : ℝ) : (⊥ : SimpleGraph (Fin 3)).IsBalanced D := by
  simp [SimpleGraph.IsBalanced]

end MathlibExt.GraphTheory.ErdosProblem1077Wanted
