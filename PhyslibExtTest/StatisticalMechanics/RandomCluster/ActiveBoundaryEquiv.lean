/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.ActiveBoundaryEquiv

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ActiveBoundaryEquiv`

On `Fin 2` with the empty graph `⊥` or the one-edge graph `⊤`, `p = 1/2`, `q = 2`:
* `restrictActive_extendActive` as a `simp` lemma;
* `activeBCZ_factorization` for the empty active graph (all edges inactive);
* `activeBCMean_eq_bcProb_lift` and `activeBCMean_boundaryClique_eq_wired` applied to the constant
  function `1` with all vertices on the boundary.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ActiveBoundaryEquiv

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- Restricting an extension gives back the active configuration.
example (ω : ConfigSpace G2.edgeSet) : restrictActive G2 (extendActive G2 ω) = ω := by simp

-- The partition function factorizes over the inactive edges.
example : bcZ (⊥ : SimpleGraph (Fin 2)) ⊥ (1 / 2) 2 =
    2 ^ ecz_NE (⊥ : SimpleGraph (Fin 2)) *
      activeBCZ (⊥ : SimpleGraph (Fin 2)) ⊥ (fun _ => 1 / 2) 2 :=
  activeBCZ_factorization _ _ _ _

-- Active expectations are expectations of the restriction under the full measure.
example : activeBCMean G2 ⊥ (fun _ => (1 / 2 : ℝ)) 2 (fun _ => 1) =
    ∑ ω : ConfigSpace (Sym2 (Fin 2)), 1 * bcProb G2 ⊥ (1 / 2) 2 ω :=
  activeBCMean_eq_bcProb_lift G2 ⊥ (by norm_num) (by norm_num) (by norm_num) _

-- With boundary-clique wiring, active expectations are wired expectations.
example : activeBCMean G2 (Lattice.boundaryCliqueGraph fun _ => True)
      (fun _ => (1 / 2 : ℝ)) 2 (fun _ => 1) =
    ∑ ω : ConfigSpace (Sym2 (Fin 2)), 1 * wiredFkProb G2 (fun _ => True) (1 / 2) 2 ω :=
  activeBCMean_boundaryClique_eq_wired G2 _ (by norm_num) (by norm_num) (by norm_num) _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ActiveBoundaryEquiv
