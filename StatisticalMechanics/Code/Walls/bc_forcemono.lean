/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Mathlib
import Code.Percolation.BurtonKeaneMerge
import Code.Percolation.TrifurcationConstruction

open Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}













theorem bc_force_mono (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) :
    removeSite (0 : Site d) ω ≤ removeSite (0 : Site d) (forceOpenFinset W ω) := by
  
  intro e
  by_cases h0 : (0 : Site d) ∈ e
  · 
    rw [removeSite_apply_of_mem h0, removeSite_apply_of_mem h0]
  · 
    
    rw [removeSite_apply_of_notMem h0, removeSite_apply_of_notMem h0]
    exact forceOpenFinset_le W ω e







theorem bc_connected_force_mono (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {a b : Site d}
    (h : Connected d (removeSite (0 : Site d) ω) a b) :
    Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) a b :=
  connected_mono (bc_force_mono ω W) h







theorem bc_cluster_force_mono (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (x : Site d) :
    cluster d (removeSite (0 : Site d) ω) x
      ⊆ cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x :=
  cluster_mono (bc_force_mono ω W) x









theorem bc_clusterInfinite_force_mono (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {x : Site d}
    (h : (cluster d (removeSite (0 : Site d) ω) x).Infinite) :
    (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x).Infinite :=
  h.mono (bc_cluster_force_mono ω W x)

end Walls

end StatMech
