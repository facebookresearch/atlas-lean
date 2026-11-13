/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























import Code.Percolation.CorridorSidesFromClusters

namespace StatMech.Walls

open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation

variable {d : ℕ}







theorem bkm_removeSiteCluster_step (ω : ConfigSpace (Sym2 (Site d))) (x z : Site d)
    {u v : Site d} (hu : u ∈ cluster d (removeSite x ω) z)
    (hadj : (openSubgraph d (removeSite x ω)).Adj u v) :
    v ∈ cluster d (removeSite x ω) z := by
  rw [mem_cluster] at hu ⊢
  exact hu.trans hadj.reachable




theorem bkm_removeSiteCluster_step_isOpenEdge (ω : ConfigSpace (Sym2 (Site d)))
    (x z : Site d) {u v : Site d} (hu : u ∈ cluster d (removeSite x ω) z)
    (hopen : IsOpenEdge d (removeSite x ω) u v) :
    v ∈ cluster d (removeSite x ω) z :=
  bkm_removeSiteCluster_step ω x z hu hopen






theorem bkm_removeSiteClusters_disjoint (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    {x' y' : Site d} (h : ¬ Connected d (removeSite x ω) x' y') :
    Disjoint (cluster d (removeSite x ω) x') (cluster d (removeSite x ω) y') := by
  rw [Set.disjoint_left]
  intro w hwx hwy
  rw [mem_cluster] at hwx hwy
  exact h (hwx.trans hwy.symm)




theorem bkm_removeSite0Clusters_disjoint (ω : ConfigSpace (Sym2 (Site d)))
    {x' y' : Site d} (h : ¬ Connected d (removeSite 0 ω) x' y') :
    Disjoint (cluster d (removeSite 0 ω) x') (cluster d (removeSite 0 ω) y') :=
  bkm_removeSiteClusters_disjoint ω 0 h

end StatMech.Walls
