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

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}










theorem bc4_adj_survives_origin_cut (ω : ConfigSpace (Sym2 (Site d))) {u w : Site d}
    (hu : u ≠ 0) (hw : w ≠ 0) (hadj : (openSubgraph d ω).Adj u w) :
    (openSubgraph d (removeSite 0 ω)).Adj u w := by
  rw [openSubgraph_adj] at hadj ⊢
  refine ⟨hadj.1, ?_⟩
  have h0not : (0 : Site d) ∉ s(u, w) := by
    rw [Sym2.mem_iff, not_or]
    exact ⟨fun h => hu h.symm, fun h => hw h.symm⟩
  rw [removeSite_apply_of_notMem h0not]
  exact hadj.2












theorem bc4_avoiding_walk_survives_origin_cut (ω : ConfigSpace (Sym2 (Site d))) {u w : Site d}
    (p : (openSubgraph d ω).Walk u w) (hp : (0 : Site d) ∉ p.support) :
    Connected d (removeSite 0 ω) u w := by
  induction p with
  | nil => exact connected_rfl
  | @cons a b c hadj p' ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hp
    obtain ⟨h0a, h0rest⟩ := hp
    
    have h0b : (0 : Site d) ≠ b := fun h => h0rest (h ▸ p'.start_mem_support)
    have hstep : (openSubgraph d (removeSite 0 ω)).Adj a b :=
      bc4_adj_survives_origin_cut ω (Ne.symm h0a) (Ne.symm h0b) hadj
    exact (SimpleGraph.Adj.reachable hstep).trans (ih h0rest)





theorem bc4_avoiding_survives_origin_cut (ω : ConfigSpace (Sym2 (Site d))) {u w : Site d}
    (h : ∃ p : (openSubgraph d ω).Walk u w, (0 : Site d) ∉ p.support) :
    Connected d (removeSite 0 ω) u w := by
  obtain ⟨p, hp⟩ := h
  exact bc4_avoiding_walk_survives_origin_cut ω p hp






theorem bc4_cluster_mono_of_avoiding (ω : ConfigSpace (Sym2 (Site d))) {u w : Site d}
    (p : (openSubgraph d ω).Walk u w) (hp : (0 : Site d) ∉ p.support) :
    w ∈ cluster d (removeSite 0 ω) u :=
  mem_cluster.mpr (bc4_avoiding_walk_survives_origin_cut ω p hp)









theorem bc4_avoiding_walk_survives_origin_cut_singleEdge (ω : ConfigSpace (Sym2 (Site d)))
    {u w : Site d} (hu : u ≠ 0) (hw : w ≠ 0) (hadj : (openSubgraph d ω).Adj u w) :
    Connected d (removeSite 0 ω) u w := by
  refine bc4_avoiding_walk_survives_origin_cut ω (hadj.toWalk) ?_
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h)
  · exact hu h.symm
  · exact hw h.symm

end Walls

end StatMech
