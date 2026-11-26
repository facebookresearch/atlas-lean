/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ContractedGraphDegree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ContractedGraphDegree`

* `bc103_reachable_deleteIncidence_of_walk_avoiding` on the complete graph on `Fin 3`: the one-edge
  walk `1 – 2` avoids `0`;
* `bc103_deg3_of_noBypass` in its conditional form with `F = G`;
* `bc103_arms_distinct_of_deleteVert_cut` and `bc103_count_of_contractedGraph` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ContractedGraphDegree

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- Deleting the edges at `0` from the complete graph on `Fin 3` keeps `1` and `2` connected.
example : ((⊤ : SimpleGraph (Fin 3)).deleteIncidenceSet 0).Reachable 1 2 :=
  bc103_reachable_deleteIncidence_of_walk_avoiding le_rfl 0
    (SimpleGraph.Walk.cons (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by decide)
      SimpleGraph.Walk.nil) (by decide)

-- Three mutually cut neighbours force degree three (with the graph as its own forest).
example {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {u v₁ v₂ v₃ : V}
    (h₁ : G.Adj u v₁) (h₂ : G.Adj u v₂) (h₃ : G.Adj u v₃)
    (c₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
    (c₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
    (c₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) : 3 ≤ G.degree u :=
  bc103_deg3_of_noBypass le_rfl (fun _ _ h => h) h₁ h₂ h₃ c₁₂ c₁₃ c₂₃

-- Mutually cut neighbours are distinct.
example {V : Type} (G : SimpleGraph V) {u v₁ v₂ v₃ : V}
    (c₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
    (c₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
    (c₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ :=
  bc103_arms_distinct_of_deleteVert_cut c₁₂ c₁₃ c₂₃

-- A contracted trifurcation graph bounds the coarse count.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (h : bc103_ContractedTrifGraph ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bc103_count_of_contractedGraph ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ContractedGraphDegree
