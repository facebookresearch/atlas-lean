/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.Lattice.Clusters

open Set
open StatMech.Lattice

namespace StatMech

namespace Walls

variable {d : ℕ}











theorem bc3_connected_of_openEdge_between {ω : ConfigSpace (Sym2 (Site d))} {x y u v : Site d}
    (hxu : Connected d ω x u) (hvy : Connected d ω y v) (huv : IsOpenEdge d ω u v) :
    Connected d ω x y :=
  hxu.trans (huv.connected.trans hvy.symm)





theorem bc3_clusters_eq_of_openEdge_between {ω : ConfigSpace (Sym2 (Site d))}
    {x y u v : Site d}
    (hxu : Connected d ω x u) (hvy : Connected d ω y v) (huv : IsOpenEdge d ω u v) :
    cluster d ω x = cluster d ω y :=
  cluster_eq_of_connected (bc3_connected_of_openEdge_between hxu hvy huv)









theorem bc3_no_crossing_pair {ω : ConfigSpace (Sym2 (Site d))} {x y u v : Site d}
    (hu : u ∈ cluster d ω x) (hv : v ∈ cluster d ω y) (huv : IsOpenEdge d ω u v) :
    cluster d ω x = cluster d ω y :=
  bc3_clusters_eq_of_openEdge_between (mem_cluster.mp hu) (mem_cluster.mp hv) huv








theorem bc3_no_crossing {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (hne : cluster d ω x ≠ cluster d ω y) :
    ∀ ⦃u : Site d⦄, u ∈ cluster d ω x → ∀ ⦃v : Site d⦄, v ∈ cluster d ω y →
      ¬ IsOpenEdge d ω u v :=
  fun _ hu _ hv huv => hne (bc3_no_crossing_pair hu hv huv)

end Walls

end StatMech
