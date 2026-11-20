/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Walls.bc6raysetdef
import Code.Percolation.Exploration

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}










theorem bc7_clusterWithin_subset_cluster (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d))
    (o : Site d) :
    clusterWithin d ω S o ⊆ cluster d ω o := by
  rintro y ⟨hyS, hoS, hconn⟩
  rw [mem_cluster]
  exact hconn.connected










theorem bc7_offBoxCluster_subset_cluster {N : ℕ} {a : Fin d} {R : ℕ}
    (ω : ConfigSpace (Sym2 (Site d))) :
    bc6_offBoxCluster N a R ω ⊆ cluster d (removeSite 0 ω) (hrHD_rayPt a (R : ℤ)) := by
  unfold bc6_offBoxCluster
  exact bc7_clusterWithin_subset_cluster (removeSite 0 ω) (box d N)ᶜ (hrHD_rayPt a (R : ℤ))



theorem bc7_offBoxCluster_connected_farEnd {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} {x : Site d}
    (hx : x ∈ bc6_offBoxCluster N a R ω) :
    Connected d (removeSite 0 ω) (hrHD_rayPt a (R : ℤ)) x :=
  bc7_offBoxCluster_subset_cluster (N := N) (a := a) (R := R) ω hx





theorem bc7_offBoxCluster_subset_cluster_self {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} {x : Site d}
    (hx : x ∈ bc6_offBoxCluster N a R ω) :
    bc6_offBoxCluster N a R ω ⊆ cluster d (removeSite 0 ω) x := by
  have hconn : Connected d (removeSite 0 ω) (hrHD_rayPt a (R : ℤ)) x :=
    bc7_offBoxCluster_connected_farEnd hx
  rw [← cluster_eq_of_connected hconn]
  exact bc7_offBoxCluster_subset_cluster (N := N) (a := a) (R := R) ω

end Walls

end StatMech
