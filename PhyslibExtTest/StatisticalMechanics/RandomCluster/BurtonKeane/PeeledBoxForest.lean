/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PeeledBoxForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PeeledBoxForest`

* `osf_spanForest` on the complete graph on `Fin 3`: it is acyclic, lies in the graph and keeps the
  reachability `0 ~ 2`;
* the double-star example `OsfDoubleStar.dsG` is acyclic with two hubs of degree `3`;
* `osf_boxOpenForest_of_peeled` in conditional form, composed with the box-open-forest count;
* refutation: `osf_PeeledBoxForest` cannot hold for every configuration and `n ≥ 1` when `d ≥ 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PeeledBoxForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

variable {d : ℕ}

-- The spanning forest of the triangle is acyclic, lies in the triangle and keeps reachability.
example : (osf_spanForest (⊤ : SimpleGraph (Fin 3))).IsAcyclic ∧
    osf_spanForest (⊤ : SimpleGraph (Fin 3)) ≤ ⊤ ∧
    (osf_spanForest (⊤ : SimpleGraph (Fin 3))).Reachable 0 2 :=
  ⟨osf_spanForest_acyclic _, osf_spanForest_le _,
    osf_spanForest_reachable _ ((SimpleGraph.top_adj 0 2).mpr (by decide))⟩

open _root_.StatMech.Percolation.OsfDoubleStar in
-- The double star of the two-trifurcation example is acyclic with two hubs of degree three.
example : dsG.IsAcyclic ∧ dsG.degree 0 = 3 ∧ dsG.degree 4 = 3 :=
  ⟨dsG_acyclic, dsG_hub0_deg, dsG_hub4_deg⟩

-- A peeled box forest gives the trifurcation count.
example (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : osf_PeeledBoxForest ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bst_Tcount_le_boundary_of_boxOpenForest ω n (osf_boxOpenForest_of_peeled ω n h)

-- No peeled box forest exists for every configuration in dimension `d ≥ 1`.
example (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → osf_PeeledBoxForest ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bst_Tcount_le_boundary_of_boxOpenForest ω n (osf_boxOpenForest_of_peeled ω n (h ω n hn))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PeeledBoxForest
