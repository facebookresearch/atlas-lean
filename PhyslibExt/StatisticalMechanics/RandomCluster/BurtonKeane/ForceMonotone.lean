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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorSidesFromClusters

/-!
# Forcing edges is monotone

Forcing a finite set of edges open can only add open edges, so connections, clusters and infinite
clusters persist, also after removing a site.

## i. Overview

`ω ≤ forceOpenFinset W ω`, and the same holds after removing any site. Hence connections, clusters
and infinite clusters of `ω` persist after forcing, with or without a removed site.

## ii. Key results

- `bc2_clusterInfinite_force_mono` : infinite clusters persist after forcing.

## iii. Table of contents

- A. Monotonicity

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Monotonicity -/

lemma bc2_force_mono_base (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) :
    ω ≤ forceOpenFinset W ω :=
  forceOpenFinset_le W ω

lemma bc2_force_mono_cut (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (x : Site d) :
    removeSite x ω ≤ removeSite x (forceOpenFinset W ω) := by
  intro e
  by_cases hx : x ∈ e
  · rw [removeSite_apply_of_mem hx, removeSite_apply_of_mem hx]
  · rw [removeSite_apply_of_notMem hx, removeSite_apply_of_notMem hx]
    exact bc2_force_mono_base ω W e

lemma bc2_force_mono_origin (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) :
    removeSite (0 : Site d) ω ≤ removeSite (0 : Site d) (forceOpenFinset W ω) :=
  bc2_force_mono_cut ω W 0

lemma bc2_connected_force_mono (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {a b : Site d}
    (h : Connected d ω a b) :
    Connected d (forceOpenFinset W ω) a b :=
  connected_mono (bc2_force_mono_base ω W) h

lemma bc2_connected_force_mono_cut (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (x : Site d) {a b : Site d}
    (h : Connected d (removeSite x ω) a b) :
    Connected d (removeSite x (forceOpenFinset W ω)) a b :=
  connected_mono (bc2_force_mono_cut ω W x) h

lemma bc2_cluster_force_mono (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (y : Site d) :
    cluster d ω y ⊆ cluster d (forceOpenFinset W ω) y :=
  cluster_mono (bc2_force_mono_base ω W) y

lemma bc2_cluster_force_mono_cut (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (x : Site d) (y : Site d) :
    cluster d (removeSite x ω) y
      ⊆ cluster d (removeSite x (forceOpenFinset W ω)) y :=
  cluster_mono (bc2_force_mono_cut ω W x) y

lemma bc2_clusterInfinite_force_mono (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {y : Site d}
    (h : (cluster d ω y).Infinite) :
    (cluster d (forceOpenFinset W ω) y).Infinite :=
  h.mono (bc2_cluster_force_mono ω W y)

lemma bc2_clusterInfinite_force_mono_cut (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (x : Site d) {y : Site d}
    (h : (cluster d (removeSite x ω) y).Infinite) :
    (cluster d (removeSite x (forceOpenFinset W ω)) y).Infinite :=
  h.mono (bc2_cluster_force_mono_cut ω W x y)

lemma bc2_connected_force_mono_origin (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {a b : Site d}
    (h : Connected d (removeSite (0 : Site d) ω) a b) :
    Connected d (removeSite (0 : Site d) (forceOpenFinset G ω)) a b :=
  bc2_connected_force_mono_cut ω G 0 h

lemma bc2_clusterInfinite_force_mono_origin (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {y : Site d}
    (h : (cluster d (removeSite (0 : Site d) ω) y).Infinite) :
    (cluster d (removeSite (0 : Site d) (forceOpenFinset G ω)) y).Infinite :=
  bc2_clusterInfinite_force_mono_cut ω G 0 h

end Walls

end StatMech
