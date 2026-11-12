/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Percolation.BurtonKeaneMerge

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}


















theorem bc8_removeSite_forceOpen_comm
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, (0 : Site d) ∈ e) :
    removeSite (0 : Site d) (forceOpenFinset F ω) = removeSite (0 : Site d) ω := by
  funext e
  by_cases h0 : (0 : Site d) ∈ e
  · 
    rw [removeSite_apply_of_mem h0, removeSite_apply_of_mem h0]
  · 
    rw [removeSite_apply_of_notMem h0, removeSite_apply_of_notMem h0]
    have hnF : e ∉ F := fun he => h0 (hF e he)
    rw [forceOpenFinset_of_notMem hnF]






theorem bc8_removeSite_forceOpen_comm_general
    (x : Site d) (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, x ∈ e) :
    removeSite x (forceOpenFinset F ω) = removeSite x ω := by
  funext e
  by_cases hx : x ∈ e
  · rw [removeSite_apply_of_mem hx, removeSite_apply_of_mem hx]
  · rw [removeSite_apply_of_notMem hx, removeSite_apply_of_notMem hx]
    have hnF : e ∉ F := fun he => hx (hF e he)
    rw [forceOpenFinset_of_notMem hnF]









theorem bc8_openSubgraph_forceOpen_eq
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, (0 : Site d) ∈ e) :
    openSubgraph d (removeSite (0 : Site d) (forceOpenFinset F ω))
      = openSubgraph d (removeSite (0 : Site d) ω) := by
  rw [bc8_removeSite_forceOpen_comm F ω hF]



theorem bc8_connected_forceOpen_iff
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, (0 : Site d) ∈ e) (u v : Site d) :
    Connected d (removeSite (0 : Site d) (forceOpenFinset F ω)) u v
      ↔ Connected d (removeSite (0 : Site d) ω) u v := by
  rw [bc8_removeSite_forceOpen_comm F ω hF]



theorem bc8_cluster_forceOpen_eq
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hF : ∀ e ∈ F, (0 : Site d) ∈ e) (a : Site d) :
    cluster d (removeSite (0 : Site d) (forceOpenFinset F ω)) a
      = cluster d (removeSite (0 : Site d) ω) a := by
  rw [bc8_removeSite_forceOpen_comm F ω hF]

end Walls

end StatMech
