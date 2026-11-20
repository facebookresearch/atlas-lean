/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Mathlib
import Code.Lattice.Clusters
import Code.Lattice.CrossingParity
import Code.RSW.Defs
import Code.Universality.HVIntersection

open Set SimpleGraph

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box













def projHom (ω : ConfigSpace (Sym2 (Site 2))) (R : Set (Site 2)) :
    (openSubgraphInduce 2 ω R) →g (hypercubicLattice 2) where
  toFun := fun v => (v : Site 2)
  map_rel' := by
    intro a b hab
    simp only [openSubgraphInduce_adj] at hab
    exact openSubgraph_le ω hab





def liftWalk (ω : ConfigSpace (Sym2 (Site 2))) (R : Set (Site 2)) {x y : R}
    (w : (openSubgraphInduce 2 ω R).Walk x y) :
    (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2) :=
  w.map (projHom ω R)




theorem liftWalk_support_mem (ω : ConfigSpace (Sym2 (Site 2))) (R : Set (Site 2))
    {x y : R} (w : (openSubgraphInduce 2 ω R).Walk x y) {z : Site 2}
    (hz : z ∈ (liftWalk ω R w).support) :
    ∃ (z' : R), z' ∈ w.support ∧ (z' : Site 2) = z := by
  have hsupp := SimpleGraph.Walk.support_map (projHom ω R) w
  obtain ⟨z', hz'_mem, hz'_eq⟩ := (List.mem_map).mp (hsupp ▸ hz)
  exact ⟨z', hz'_mem, hz'_eq⟩













def colLeq (k : ℤ) : Set (Site 2) := {z | z 0 ≤ k}

@[simp] theorem mem_colLeq (k : ℤ) (z : Site 2) : z ∈ colLeq k ↔ z 0 ≤ k := Iff.rfl





theorem exists_bdEdge_colLeq {k α β : ℤ} {x y : Site 2}
    (hx : x 0 = α) (hy : y 0 = β) (hk1 : α ≤ k) (hk2 : k < β)
    (w : (hypercubicLattice 2).Walk x y) :
    ∃ e ∈ w.edges, bdEdge (colLeq k) e := by
  classical
  have hodd : ¬ Even (crossCount (colLeq k) w) := by
    rw [crossCount_parity]
    intro h
    have hxT : x ∈ colLeq k := by rw [mem_colLeq, hx]; omega
    have hyT : y ∉ colLeq k := by rw [mem_colLeq, hy]; omega
    exact hyT (h.mp hxT)
  by_contra hcon
  apply hodd
  have hz : crossCount (colLeq k) w = 0 := by
    rw [crossCount, List.countP_eq_zero]
    intro e he
    simp only [decide_eq_true_eq]
    exact fun hb => hcon ⟨e, he, hb⟩
  rw [hz]
  exact ⟨0, rfl⟩






theorem hwalk_meets_column {k α β : ℤ} {x y : Site 2}
    (hx : x 0 = α) (hy : y 0 = β) (hk1 : α ≤ k) (hk2 : k < β)
    (w : (hypercubicLattice 2).Walk x y) :
    ∃ z ∈ w.support, z 0 = k := by
  obtain ⟨e, hemem, hebd⟩ := exists_bdEdge_colLeq hx hy hk1 hk2 w
  induction e with
  | h u v =>
    rw [bdEdge_mk] at hebd
    have hadj := w.adj_of_mem_edges hemem
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    simp only [mem_colLeq] at hebd
    have hu : u ∈ w.support := w.fst_mem_support_of_mem_edges hemem
    have hv : v ∈ w.support := w.snd_mem_support_of_mem_edges hemem
    by_cases huk : u 0 ≤ k
    · 
      have hvk : ¬ v 0 ≤ k := by rw [← hebd]; exact huk
      have hdiff : (u 0 - v 0).natAbs ≤ 1 := by omega
      exact ⟨u, hu, by omega⟩
    · 
      have hvk : v 0 ≤ k := by by_contra hc; exact huk (hebd.mpr hc)
      have hdiff : (u 0 - v 0).natAbs ≤ 1 := by omega
      exact ⟨v, hv, by omega⟩













theorem boxCrossing_meets_column (ω : ConfigSpace (Sym2 (Site 2)))
    {α β c d k : ℤ} (hk1 : α ≤ k) (hk2 : k < β)
    {x y : rect α β c d} (hx0 : (x : Site 2) 0 = α) (hy0 : (y : Site 2) 0 = β)
    (w : (openSubgraphInduce 2 ω (rect α β c d)).Walk x y) :
    ∃ z ∈ w.support, (z : Site 2) 0 = k := by
  obtain ⟨zs, hzsmem, hzscol⟩ :=
    hwalk_meets_column hx0 hy0 hk1 hk2 (liftWalk ω (rect α β c d) w)
  obtain ⟨z, hz_mem, hz_eq⟩ := liftWalk_support_mem ω (rect α β c d) w hzsmem
  exact ⟨z, hz_mem, by rw [hz_eq]; exact hzscol⟩

end Universality

end StatMech
