/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib
import Code.Lattice.EarContraction

open SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice












def jc_IsPendantCell (K : Set (Site 2)) (c : Site 2) : Prop :=
  c ∈ K ∧ ∃! u : Site 2, u ∈ K ∧ (hypercubicLattice 2).Adj c u












theorem jc_pendant_existsUnique_induce (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (h : ∃! u : Site 2, u ∈ K ∧ (hypercubicLattice 2).Adj c u) :
    ∃! u : ↑K, ((hypercubicLattice 2).induce K).Adj ⟨c, hc⟩ u := by
  obtain ⟨u, ⟨huK, hadj⟩, huniq⟩ := h
  refine ⟨⟨u, huK⟩, ?_, ?_⟩
  · simp only [SimpleGraph.induce_adj]; exact hadj
  · rintro ⟨w, hwK⟩ hw
    simp only [SimpleGraph.induce_adj] at hw
    exact Subtype.ext (huniq w ⟨hwK, hw⟩)




theorem jc_pendant_nbr_finite (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (h : ∃! u : ↑K, ((hypercubicLattice 2).induce K).Adj ⟨c, hc⟩ u) :
    (((hypercubicLattice 2).induce K).neighborSet ⟨c, hc⟩).Finite := by
  obtain ⟨u, _, huniq⟩ := h
  apply Set.Finite.subset (Set.finite_singleton u)
  intro x hx
  rw [SimpleGraph.mem_neighborSet] at hx
  exact Set.mem_singleton_iff.mpr (huniq x hx)
















theorem jc_cellConnected_diff_of_pendant (K : Set (Site 2)) (c : Site 2)
    (hconn : CellConnected K) (hpend : jc_IsPendantCell K c) :
    CellConnected (K \ {c}) := by
  obtain ⟨hc, hunique⟩ := hpend
  have hadj := jc_pendant_existsUnique_induce K c hc hunique
  letI : Fintype ↑(((hypercubicLattice 2).induce K).neighborSet ⟨c, hc⟩) :=
    (jc_pendant_nbr_finite K c hc hadj).fintype
  apply cellConnected_diff_of_degree_one K c hc hconn
  rw [degree_eq_one_iff_existsUnique_adj]
  exact hadj





theorem jc_leafRemoval (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (hconn : CellConnected K)
    (hunique : ∃! u : Site 2, u ∈ K ∧ (hypercubicLattice 2).Adj c u) :
    CellConnected (K \ {c}) :=
  jc_cellConnected_diff_of_pendant K c hconn ⟨hc, hunique⟩








noncomputable def jc_domino : Set (Site 2) := {![0, 0], ![1, 0]}

theorem jc_mem_domino (v : Site 2) : v ∈ jc_domino ↔ v = ![0, 0] ∨ v = ![1, 0] := by
  unfold jc_domino; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem jc_domino_00 : (![0, 0] : Site 2) ∈ jc_domino := by rw [jc_mem_domino]; tauto
theorem jc_domino_10 : (![1, 0] : Site 2) ∈ jc_domino := by rw [jc_mem_domino]; tauto



theorem jc_domino_cellConnected : CellConnected jc_domino := by
  rw [CellConnected, SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨![0, 0], jc_domino_00⟩⟩⟩
  have e : ((hypercubicLattice 2).induce jc_domino).Adj ⟨![0, 0], jc_domino_00⟩
      ⟨![1, 0], jc_domino_10⟩ := by
    rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have r0 : ∀ x : ↑jc_domino,
      ((hypercubicLattice 2).induce jc_domino).Reachable ⟨![0, 0], jc_domino_00⟩ x := by
    rintro ⟨x, hx⟩
    rw [jc_mem_domino] at hx
    rcases hx with h | h <;> subst h
    · rfl
    · exact e.reachable
  intro a b
  exact (r0 a).symm.trans (r0 b)



theorem jc_domino_pendant_origin : jc_IsPendantCell jc_domino ![0, 0] := by
  refine ⟨jc_domino_00, ![1, 0], ⟨jc_domino_10, ?_⟩, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rintro w ⟨hwd, hadj⟩
    rw [jc_mem_domino] at hwd
    rcases hwd with h | h
    · subst h; rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj; norm_num at hadj
    · exact h



theorem jc_domino_leaf_removal : CellConnected (jc_domino \ {![0, 0]}) :=
  jc_cellConnected_diff_of_pendant jc_domino ![0, 0] jc_domino_cellConnected
    jc_domino_pendant_origin

end Walls

end StatMech
