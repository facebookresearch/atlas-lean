/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Algebra.Ring.Int.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting

/-!
# Three axis corridors

Axis lines through the origin along distinct axes meet only at the origin, so in `d ≥ 3` there are
three axis corridors with pairwise disjoint edges.

## i. Overview

`corridorRay j` is the line of sites `t e_j`, `t ∈ ℤ`. Corridor edges lie on it, and lines along
distinct axes meet only at the origin, so corridors along distinct axes have disjoint edge sets. In
`d ≥ 3` the axes `0`, `1`, `2` are distinct, which gives three such corridors.

## ii. Key results

- `bkm_corridorRay_inter_eq_origin` : lines along distinct axes meet only at the origin.
- `bkm_dcc_three_axes` : three pairwise disjoint axis corridors in `d ≥ 3`.

## iii. Table of contents

- A. Axis lines
- B. Three axes

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Axis lines -/

/-- The line of sites `t e_j`, `t ∈ ℤ`, along axis `j`. -/
def corridorRay (j : Fin d) : Set (Site d) := {x | ∃ t : ℤ, x = hrHD_rayPt j t}

lemma origin_mem_corridorRay (j : Fin d) : (0 : Site d) ∈ corridorRay j :=
  ⟨0, by simp⟩

lemma rayPt_mem_corridorRay (j : Fin d) (t : ℤ) : hrHD_rayPt j t ∈ corridorRay j :=
  ⟨t, rfl⟩

lemma corridorEdge_subset_corridorRay {j : Fin d} (t : ℤ) :
    ∀ y ∈ (s(hrHD_rayPt j t, hrHD_rayPt j (t + 1)) : Sym2 (Site d)),
      y ∈ corridorRay j := by
  intro y hy
  rw [Sym2.mem_iff] at hy
  rcases hy with rfl | rfl
  · exact rayPt_mem_corridorRay j _
  · exact rayPt_mem_corridorRay j _

/-! ## B. Three axes -/

lemma bkm_three_axes_distinct (hd : 3 ≤ d) :
    (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ ∧
    (⟨0, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ ∧
    (⟨1, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · intro h; simp [Fin.ext_iff] at h

lemma bkm_corridorRay_inter_eq_origin {i j : Fin d} (h : i ≠ j) :
    corridorRay i ∩ corridorRay j = {(0 : Site d)} := by
  ext x
  simp only [Set.mem_inter_iff, corridorRay, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    by_cases hs : s = 0
    · subst hs; simp
    · exact absurd ht (hrHD_rayPt_disjoint_of_ne h hs)
  · rintro rfl
    exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩

lemma bkm_corridorRay_disjoint_off_origin {i j : Fin d} (h : i ≠ j) {x : Site d}
    (hx : x ≠ 0) : ¬ (x ∈ corridorRay i ∧ x ∈ corridorRay j) := by
  intro hmem
  have : x ∈ ({(0 : Site d)} : Set (Site d)) := by
    rw [← bkm_corridorRay_inter_eq_origin h]; exact hmem
  exact hx (Set.mem_singleton_iff.mp this)

lemma bkm_corridorEdges_disjoint_of_ne {i j : Fin d} (h : i ≠ j) (L : ℕ) :
    Disjoint (hrHD_corridorEdges i L) (hrHD_corridorEdges j L) := by
  rw [Finset.disjoint_left]
  intro e hei hej
  rw [hrHD_corridorEdges, Finset.mem_image] at hei hej
  obtain ⟨s, _, hse⟩ := hei
  obtain ⟨t, _, hte⟩ := hej
  have hj0 : ∀ y ∈ e, y i = 0 := by
    rw [← hte]
    intro y hy
    rw [Sym2.mem_iff] at hy
    rcases hy with rfl | rfl <;> exact hrHD_rayPt_of_ne j _ h
  have hmem : hrHD_rayPt i ((s : ℤ) + 1) ∈ e := by
    rw [← hse]; exact Sym2.mem_mk_right _ _
  have := hj0 _ hmem
  rw [hrHD_rayPt_self] at this
  omega

lemma bkm_dcc_three_axes (hd : 3 ≤ d) :
    ∃ j₁ j₂ j₃ : Fin d,
      (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
      (corridorRay j₁ ∩ corridorRay j₂ = {(0 : Site d)} ∧
        corridorRay j₁ ∩ corridorRay j₃ = {(0 : Site d)} ∧
        corridorRay j₂ ∩ corridorRay j₃ = {(0 : Site d)}) ∧
      (∀ L : ℕ, Disjoint (hrHD_corridorEdges j₁ L) (hrHD_corridorEdges j₂ L) ∧
        Disjoint (hrHD_corridorEdges j₁ L) (hrHD_corridorEdges j₃ L) ∧
        Disjoint (hrHD_corridorEdges j₂ L) (hrHD_corridorEdges j₃ L)) := by
  obtain ⟨j₁, j₂, j₃, h12, h13, h23⟩ := hrHD_exists_three_independent_axes hd
  exact ⟨j₁, j₂, j₃, ⟨h12, h13, h23⟩,
    ⟨bkm_corridorRay_inter_eq_origin h12, bkm_corridorRay_inter_eq_origin h13,
      bkm_corridorRay_inter_eq_origin h23⟩,
    fun L => ⟨bkm_corridorEdges_disjoint_of_ne h12 L, bkm_corridorEdges_disjoint_of_ne h13 L,
      bkm_corridorEdges_disjoint_of_ne h23 L⟩⟩

end StatMech.Walls
