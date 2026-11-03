/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjection

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjection`

* the explicit star and path witnesses `fli_star_hall`, `fli_star_injection`,
  `fli_path_injection`;
* `fli_mem_satSet_of_mem` and `fli_satSet_closed_adj` on the star;
* `fli_distinctArmEnds_of_boxOpenForest` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjection

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Hall's condition for the star: its centre reaches a leaf.
example : ({0} : Finset (Fin 4)).card ≤
    (({0} : Finset (Fin 4)).biUnion (fun x => Finset.univ.filter
      (fun ℓ => Flc2Witness.starG.degree ℓ = 1 ∧ Flc2Witness.starG.Reachable x ℓ))).card :=
  fli_star_hall

-- An injection from the star's branch vertex to a reachable leaf.
example : ∃ ψ : Fin 4 → Fin 4, (∀ x ∈ ({0} : Finset (Fin 4)),
    Flc2Witness.starG.degree (ψ x) = 1 ∧ Flc2Witness.starG.Reachable x (ψ x)) ∧
    Set.InjOn ψ ({0} : Finset (Fin 4)) :=
  fli_star_injection

-- The path has no branch vertex, so the empty injection works.
example : ∃ ψ : Fin 2 → Fin 2, (∀ x ∈ (∅ : Finset (Fin 2)),
    Flc2Witness.pathG.degree (ψ x) = 1 ∧ Flc2Witness.pathG.Reachable x (ψ x)) ∧
    Set.InjOn ψ (∅ : Finset (Fin 2)) :=
  fli_path_injection

-- The saturation of `{0}` contains `0` and is closed under adjacency.
example (w : Fin 4) (h : Flc2Witness.starG.Adj 0 w) :
    w ∈ fli_satSet Flc2Witness.starG ({0} : Finset (Fin 4)) :=
  fli_satSet_closed_adj _ h (fli_mem_satSet_of_mem _ (Finset.mem_singleton_self 0))

-- A box open forest yields distinct arm ends.
example (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) (h : bst_BoxOpenForest ω n) :
    tfc_DistinctArmEnds ω n :=
  fli_distinctArmEnds_of_boxOpenForest ω n h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjection
