/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationExistence

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationExistence`

* `tre_branch_distinct_of_regions` on the all-closed configuration with no forced edges: the
  singleton regions `{a}` and `{b}` of distinct sites give distinct clusters after removing the
  origin;
* `tre_forceOpenFinset_comp`: forcing twice is forcing the union;
* `tre_removeSite_forceOpen_comm` for a forced edge avoiding the origin;
* `tre_mergeFreeInsertionRho_of_reachOrigin` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationExistence

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation
open _root_.StatMech.ConfigSpace MeasureTheory

variable {d : ℕ}

-- Disjoint closed regions keep the branches distinct.
example (a b : Site d) (hab : a ≠ b) :
    cluster d (removeSite 0 (forceOpenFinset ∅ (fun _ => false))) a
      ≠ cluster d (removeSite 0 (forceOpenFinset ∅ (fun _ => false))) b :=
  tre_branch_distinct_of_regions _ ∅ a b {a} {b} rfl rfl
    (fun _ _ _ h => absurd h.2 Bool.false_ne_true) (fun _ _ _ h => absurd h (Finset.notMem_empty _))
    (fun _ _ _ h => absurd h.2 Bool.false_ne_true) (fun _ _ _ h => absurd h (Finset.notMem_empty _))
    (Set.disjoint_singleton.mpr hab)

-- Forcing `W` and then `F` is forcing `F ∪ W`.
example (F W : Finset (Sym2 (Site d))) :
    forceOpenFinset F (forceOpenFinset W (fun _ => false)) =
      forceOpenFinset (F ∪ W) (fun _ => false) :=
  tre_forceOpenFinset_comp F W _

-- Removing the origin commutes with forcing an edge that avoids it.
example (y z : Site d) (hy : y ≠ 0) (hz : z ≠ 0) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite 0 (forceOpenFinset {s(y, z)} ω) = forceOpenFinset {s(y, z)} (removeSite 0 ω) :=
  tre_removeSite_forceOpen_comm _ (by simp [Sym2.mem_iff, hy.symm, hz.symm]) ω

-- The reach-origin condition gives the variant insertion.
example (ω : ConfigSpace (Sym2 (Site d))) (h : mco_ThreeClustersReachOrigin ω) :
    tre_MergeFreeInsertionRho ω :=
  tre_mergeFreeInsertionRho_of_reachOrigin ω h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationExistence
