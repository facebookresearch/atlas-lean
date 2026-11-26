/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Sym.Sym2
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OffBoxRaySet

/-!
# No open edge between distinct cut clusters

In the configuration without the origin, an open edge between two clusters merges them, so no open
edge joins distinct clusters.

## i. Overview

If `u` is in the cut cluster of `x`, `v` in that of `y`, and `u — v` is open in `removeSite 0 ω`,
then `x` and `y` are connected and their clusters agree. Hence no open edge joins distinct cut
clusters, and an open edge from a cluster stays in it. The same holds for the off-box clusters along
axis rays.

## ii. Key results

- `bc7_cut_no_crossing` : no open edge between distinct cut clusters.
- `bc7_offBoxCluster_no_crossing` : the same for off-box clusters.

## iii. Table of contents

- A. Cut clusters
- B. Off-box clusters

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Cut clusters -/

lemma bc7_cut_connected_of_openEdge_between {ω : ConfigSpace (Sym2 (Site d))}
    {x y u v : Site d}
    (hxu : Connected d (removeSite 0 ω) x u) (hvy : Connected d (removeSite 0 ω) y v)
    (huv : IsOpenEdge d (removeSite 0 ω) u v) :
    Connected d (removeSite 0 ω) x y :=
  hxu.trans (huv.connected.trans hvy.symm)

lemma bc7_cut_clusters_eq_of_openEdge_between {ω : ConfigSpace (Sym2 (Site d))}
    {x y u v : Site d}
    (hxu : Connected d (removeSite 0 ω) x u) (hvy : Connected d (removeSite 0 ω) y v)
    (huv : IsOpenEdge d (removeSite 0 ω) u v) :
    cluster d (removeSite 0 ω) x = cluster d (removeSite 0 ω) y :=
  cluster_eq_of_connected (bc7_cut_connected_of_openEdge_between hxu hvy huv)

lemma bc7_cut_no_crossing_pair {ω : ConfigSpace (Sym2 (Site d))} {x y u v : Site d}
    (hu : u ∈ cluster d (removeSite 0 ω) x) (hv : v ∈ cluster d (removeSite 0 ω) y)
    (huv : IsOpenEdge d (removeSite 0 ω) u v) :
    cluster d (removeSite 0 ω) x = cluster d (removeSite 0 ω) y :=
  bc7_cut_clusters_eq_of_openEdge_between (mem_cluster.mp hu) (mem_cluster.mp hv) huv

lemma bc7_cut_no_crossing {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y) :
    ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
      ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
        ¬ IsOpenEdge d (removeSite 0 ω) u v :=
  fun _ hu _ hv huv => hne (bc7_cut_no_crossing_pair hu hv huv)

lemma bc7_cut_no_crossing_set {ω : ConfigSpace (Sym2 (Site d))} {x y u v : Site d}
    (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y)
    (hu : u ∈ cluster d (removeSite 0 ω) x)
    (huv : IsOpenEdge d (removeSite 0 ω) u v) :
    v ∉ cluster d (removeSite 0 ω) y :=
  fun hv => bc7_cut_no_crossing hne hu hv huv

lemma bc7_cut_edge_stays_in_cluster {ω : ConfigSpace (Sym2 (Site d))} {x u v : Site d}
    (hu : u ∈ cluster d (removeSite 0 ω) x)
    (huv : IsOpenEdge d (removeSite 0 ω) u v) :
    v ∈ cluster d (removeSite 0 ω) x :=
  mem_cluster.mpr ((mem_cluster.mp hu).trans huv.connected)

/-! ## B. Off-box clusters -/

lemma bc7_offBoxCluster_mem_cutCluster {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} {x : Site d}
    (hx : x ∈ bc6_offBoxCluster N a R ω) :
    x ∈ cluster d (removeSite 0 ω) (hrHD_rayPt a (R : ℤ)) := by
  obtain ⟨_hxS, _hoS, hconn⟩ := hx
  exact mem_cluster.mpr hconn.connected

lemma bc7_offBoxCluster_no_crossing {N : ℕ} {a c : Fin d} {Ra Rc : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))}
    (hne : cluster d (removeSite 0 ω) (hrHD_rayPt a (Ra : ℤ)) ≠
        cluster d (removeSite 0 ω) (hrHD_rayPt c (Rc : ℤ)))
    {u v : Site d}
    (hu : u ∈ bc6_offBoxCluster N a Ra ω) (hv : v ∈ bc6_offBoxCluster N c Rc ω) :
    ¬ IsOpenEdge d (removeSite 0 ω) u v :=
  bc7_cut_no_crossing hne (bc7_offBoxCluster_mem_cutCluster hu)
    (bc7_offBoxCluster_mem_cutCluster hv)

end Walls

end StatMech
