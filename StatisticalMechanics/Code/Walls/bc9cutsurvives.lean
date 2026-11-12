/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.BurtonKeaneMerge
import Code.Walls.bc8removeforcecomm

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}



















theorem bc9_removeSite_le_forceOpen
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite (0 : Site d) ω ≤ removeSite (0 : Site d) (forceOpenFinset W ω) := by
  intro e
  by_cases h0 : (0 : Site d) ∈ e
  · 
    rw [removeSite_apply_of_mem h0, removeSite_apply_of_mem h0]
  · 
    rw [removeSite_apply_of_notMem h0, removeSite_apply_of_notMem h0]
    exact forceOpenFinset_le W ω e










theorem bc9_cutCluster_subset
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    cluster d (removeSite (0 : Site d) ω) x
      ⊆ cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x :=
  cluster_mono (bc9_removeSite_le_forceOpen W ω) x



theorem bc9_connected_of_base
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (h : Connected d (removeSite (0 : Site d) ω) x y) :
    Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y :=
  connected_mono (bc9_removeSite_le_forceOpen W ω) h





theorem bc9_cutCluster_survives_infinite
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hinf : (cluster d (removeSite (0 : Site d) ω) x).Infinite) :
    (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x).Infinite :=
  hinf.mono (bc9_cutCluster_subset W ω x)










theorem bc9_reaches_shares_cluster
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (h : Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y) :
    cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x
      = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y :=
  cluster_eq_of_connected h






theorem bc9_reaches_shares_infinite
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hinf : (cluster d (removeSite (0 : Site d) ω) x).Infinite)
    (h : Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y) :
    cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y
      = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x ∧
      (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y).Infinite := by
  have heq := (bc9_reaches_shares_cluster W ω h).symm
  exact ⟨heq, heq ▸ bc9_cutCluster_survives_infinite W ω hinf⟩




















theorem bc9_cut_survives
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (_hW : ∀ e ∈ W, (0 : Site d) ∉ e) {x : Site d}
    (hinf : (cluster d (removeSite (0 : Site d) ω) x).Infinite) :
    (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x).Infinite ∧
    ∀ y, Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y →
      cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y
        = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x ∧
      (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y).Infinite :=
  ⟨bc9_cutCluster_survives_infinite W ω hinf,
   fun _y h => bc9_reaches_shares_infinite W ω hinf h⟩

















theorem bc9_origin_isolated_of_avoiding
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (_hW : ∀ e ∈ W, (0 : Site d) ∉ e) (v : Site d) :
    ¬ (openSubgraph d (removeSite (0 : Site d) (forceOpenFinset W ω))).Adj 0 v := by
  rw [openSubgraph_adj]
  rintro ⟨_hadj, hopen⟩
  
  have h0mem : (0 : Site d) ∈ s((0 : Site d), v) := Sym2.mem_mk_left 0 v
  rw [removeSite_apply_of_mem h0mem] at hopen
  exact absurd hopen (by simp)











theorem bc9_cut_survives_self
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hW : ∀ e ∈ W, (0 : Site d) ∉ e)
    (hinf : (cluster d (removeSite (0 : Site d) ω) 0).Infinite) :
    (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) 0).Infinite ∧
    ∀ y, Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) 0 y →
      cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y
        = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) 0 ∧
      (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y).Infinite :=
  bc9_cut_survives W ω hW hinf















theorem bc9_cutCluster_eq_of_originIncident
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, (0 : Site d) ∈ e) (a : Site d) :
    cluster d (removeSite (0 : Site d) (forceOpenFinset F ω)) a
      = cluster d (removeSite (0 : Site d) ω) a :=
  bc8_cluster_forceOpen_eq F ω hF a



section AxiomAudit


#guard_msgs in
#print axioms bc9_removeSite_le_forceOpen


#guard_msgs in
#print axioms bc9_cutCluster_survives_infinite


#guard_msgs in
#print axioms bc9_cut_survives


#guard_msgs in
#print axioms bc9_origin_isolated_of_avoiding

end AxiomAudit

end Walls

end StatMech
