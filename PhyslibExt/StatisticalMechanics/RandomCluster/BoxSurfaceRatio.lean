/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import PhyslibExt.CondensedMatter.IsingModel.InfiniteVolume
public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolume

/-!
# Box surface-to-volume ratio

Counts of boundary vertices and edges of the box `Λ_n` and the vanishing of its surface-to-volume
ratio.

## i. Overview

The boundary vertex and edge counts of `boxGraph d n` match the closed-form counts of
`BoxSurfaceVolume`, so `|∂Λ_n| / |E(Λ_n)| → 0` for `d ≥ 1`.

## ii. Key results

- `fup_boundary_card_eq`, `fup_edge_card_eq` : boundary and edge counts of the box graph.
- `fup_surfaceVolume_tendsto_zero` : `|∂Λ_n| / |E(Λ_n)| → 0`.

## iii. Table of contents

- A. Counting boundary vertices and edges

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 4.63.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}

/-! ## A. Counting boundary vertices and edges -/

lemma fup_boundary_card_eq (d n : ℕ) :
    (Finset.univ.filter (boxBoundary d n)).card = boxSV_boundaryCard d n := by
  classical
  unfold boxSV_boundaryCard
  rw [← boxSV_vbF_eq_toFinset]
  apply Finset.card_nbij (fun x : boxVerts d n => (x : Site d))
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
    rw [Finset.mem_coe, boxSV_vbF_eq_toFinset, Set.Finite.mem_toFinset]
    exact ha
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    rw [Finset.mem_coe, boxSV_vbF_eq_toFinset, Set.Finite.mem_toFinset] at hb
    have hbbox : b ∈ box d n := (Set.sdiff_subset) hb
    refine ⟨⟨b, hbbox⟩, ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact hb

lemma fup_dart_card_eq (d n : ℕ) :
    Fintype.card (boxGraph d n).Dart = boxSV_edgeCard d n := by
  classical
  unfold boxSV_edgeCard
  rw [← Fintype.card_coe (boxSV_edgeF d n)]
  apply Fintype.card_congr
  refine Equiv.ofBijective (fun D => ⟨((D.toProd.1 : Site d), (D.toProd.2 : Site d)), ?_⟩) ?_
  · have hadj : (hypercubicLattice d).Adj (D.toProd.1 : Site d) (D.toProd.2 : Site d) :=
      (SimpleGraph.comap_adj).mp D.adj
    rw [boxSV_mem_edgeF]
    refine ⟨?_, ?_, hadj⟩
    · rw [boxSV_mem_boxF]; intro i; dsimp only
      have := (D.toProd.1).2 i; rw [Finset.mem_Icc]; constructor <;> omega
    · rw [boxSV_mem_boxF]; intro i; dsimp only
      have := (D.toProd.2).2 i; rw [Finset.mem_Icc]; constructor <;> omega
  · constructor
    · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, e⟩, hce⟩ heq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      have ha : a = c := Subtype.ext h1
      have hb : b = e := Subtype.ext h2
      subst ha; subst hb; rfl
    · rintro ⟨⟨x, y⟩, hmem⟩
      rw [boxSV_mem_edgeF] at hmem
      obtain ⟨hx, hy, hadj⟩ := hmem
      rw [boxSV_mem_boxF] at hx hy
      dsimp only at hx hy
      have hxbox : x ∈ box d n := by
        intro i; have := hx i; rw [Finset.mem_Icc] at this
        change (x i).natAbs ≤ n; omega
      have hybox : y ∈ box d n := by
        intro i; have := hy i; rw [Finset.mem_Icc] at this
        change (y i).natAbs ≤ n; omega
      have hcadj : (boxGraph d n).Adj (⟨x, hxbox⟩ : boxVerts d n) ⟨y, hybox⟩ :=
        (SimpleGraph.comap_adj).mpr hadj
      exact ⟨⟨(⟨x, hxbox⟩, ⟨y, hybox⟩), hcadj⟩, rfl⟩

lemma fup_edge_card_eq (d n : ℕ) :
    boxSV_edgeCard d n = 2 * (boxGraph d n).edgeFinset.card := by
  rw [← fup_dart_card_eq d n]
  exact SimpleGraph.dart_card_eq_twice_card_edges (boxGraph d n)

lemma fup_surfaceVolume_tendsto_zero (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n =>
        ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ))
      atTop (𝓝 0) := by
  have hbase := boxSV_ratio_tendsto_zero d hd
  have heq : ∀ n,
      ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)
      = 2 * ((boxSV_boundaryCard d n : ℝ) / (boxSV_edgeCard d n : ℝ)) := by
    intro n
    rw [fup_boundary_card_eq d n, fup_edge_card_eq d n]
    by_cases hE : (boxGraph d n).edgeFinset.card = 0
    · rw [hE]; push_cast; simp
    · have hEpos : (0 : ℝ) < (boxGraph d n).edgeFinset.card := by
        have : (boxGraph d n).edgeFinset.card ≠ 0 := hE
        positivity
      push_cast
      field_simp
  have hmul : Tendsto
      (fun n => 2 * ((boxSV_boundaryCard d n : ℝ) / (boxSV_edgeCard d n : ℝ)))
      atTop (𝓝 (2 * 0)) := hbase.const_mul 2
  rw [mul_zero] at hmul
  exact hmul.congr (fun n => (heq n).symm)

end FK

end StatMech
