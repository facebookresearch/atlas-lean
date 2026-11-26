/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Sym.Sym2
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness

/-!
# Removing the origin after forcing edges at the origin

If every forced edge contains the origin, forcing them open and then removing the origin is the same
as just removing the origin.

## i. Overview

`removeSite 0` closes every edge at the origin, so it erases the effect of `forceOpenFinset F`
whenever every edge of `F` contains the origin. In general removing a site commutes with forcing
edges that avoid it. Consequently open subgraphs, connectivity and clusters after removing the
origin do not see such forced edges.

## ii. Key results

- `bc8_removeSite_forceOpen_comm` : removal erases forced edges at the origin
- `bc8_removeSite_forceOpen_comm_general` : removal commutes with forcing edges that avoid the site
- `bc8_cluster_forceOpen_eq` : clusters after removal ignore the forced edges

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Results -/

lemma bc8_removeSite_forceOpen_comm
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, (0 : Site d) ∈ e) :
    removeSite (0 : Site d) (forceOpenFinset F ω) = removeSite (0 : Site d) ω := by
  funext e
  by_cases h0 : (0 : Site d) ∈ e
  · rw [removeSite_apply_of_mem h0, removeSite_apply_of_mem h0]
  · rw [removeSite_apply_of_notMem h0, removeSite_apply_of_notMem h0]
    have hnF : e ∉ F := fun he => h0 (hF e he)
    rw [forceOpenFinset_of_notMem hnF]

lemma bc8_removeSite_forceOpen_comm_general
    (x : Site d) (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, x ∈ e) :
    removeSite x (forceOpenFinset F ω) = removeSite x ω := by
  funext e
  by_cases hx : x ∈ e
  · rw [removeSite_apply_of_mem hx, removeSite_apply_of_mem hx]
  · rw [removeSite_apply_of_notMem hx, removeSite_apply_of_notMem hx]
    have hnF : e ∉ F := fun he => hx (hF e he)
    rw [forceOpenFinset_of_notMem hnF]

lemma bc8_openSubgraph_forceOpen_eq
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, (0 : Site d) ∈ e) :
    openSubgraph d (removeSite (0 : Site d) (forceOpenFinset F ω))
      = openSubgraph d (removeSite (0 : Site d) ω) := by
  rw [bc8_removeSite_forceOpen_comm F ω hF]

lemma bc8_connected_forceOpen_iff
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, (0 : Site d) ∈ e) (u v : Site d) :
    Connected d (removeSite (0 : Site d) (forceOpenFinset F ω)) u v
      ↔ Connected d (removeSite (0 : Site d) ω) u v := by
  rw [bc8_removeSite_forceOpen_comm F ω hF]

lemma bc8_cluster_forceOpen_eq
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, (0 : Site d) ∈ e) (a : Site d) :
    cluster d (removeSite (0 : Site d) (forceOpenFinset F ω)) a
      = cluster d (removeSite (0 : Site d) ω) a := by
  rw [bc8_removeSite_forceOpen_comm F ω hF]

end Walls

end StatMech
