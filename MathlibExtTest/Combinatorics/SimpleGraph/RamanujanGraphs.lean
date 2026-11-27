/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.RamanujanGraphs
import Mathlib.Tactic.NormNum

open MathlibExt.GraphTheory.RamanujanGraphsWanted

open Classical in
/-- At the minimum degree, the theorem bounds the second eigenvalue of a large graph. -/
example : ∃ (n : ℕ) (hn : 100 ≤ n) (G : SimpleGraph (Fin n)),
    G.IsRegularOfDegree 3 ∧ G.Colorable 2 ∧
      |(G.isHermitian_adjMatrix (R := ℝ)).eigenvalues₀
        ⟨1, by simp only [Fintype.card_fin]; omega⟩| ≤ 2 * Real.sqrt 2 := by
  obtain ⟨n, hn, G, hreg, hcolor, hbound⟩ :=
    exists_bipartite_ramanujan (d := 3) (hd := le_rfl) (N := 100)
  refine ⟨n, hn, G, hreg, hcolor, ?_⟩
  let i : Fin (Fintype.card (Fin n)) := ⟨1, by simp only [Fintype.card_fin]; omega⟩
  have h := hbound i (by change (1 : ℕ) ≠ 0; decide) (by change 1 + 1 ≠ n; omega)
  norm_num at h
  exact h
