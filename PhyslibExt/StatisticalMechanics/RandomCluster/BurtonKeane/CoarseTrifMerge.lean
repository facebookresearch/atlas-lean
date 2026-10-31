/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Filter.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifRecenter

/-!
# Recentred merges on ℤ²

When three infinite clusters meet a box of radius `n ≤ L`, they give a coarse trifurcation at scale
`L`; this gives the recentred merge and the coarse step at some scale.

## i. Overview

The box of radius `n` lies in the `L`-box at the origin when `n ≤ L`, so three distinct infinite
clusters meeting it give a coarse trifurcation at scale `L` after forcing. This gives the recentred
merge `bc119_RecenterBoxMerge 2 L n` for `n ≤ L`, in particular on the diagonal, and for a
translation-invariant measure with finite energy the coarse step at scale `n` and at some scale.

## ii. Key results

- `bkm_recenterBoxMerge_of_le` : the recentred merge for `n ≤ L`.
- `bkm_coarseTrifExistence_atSomeScale` : the coarse step at some scale.

## iii. Table of contents

- A. Boxes inside the coarse box
- B. The coarse step

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Boxes inside the coarse box -/

lemma bkm_box_subset_boxAround {L n : ℕ} (hnL : n ≤ L) {x : Site 2} (hx : x ∈ box 2 n) :
    x ∈ bc61_boxAround 2 L 0 := by
  rw [bc61_mem_boxAround_zero]
  exact box_mono 2 hnL hx

lemma bkm_coarseTrif_of_le {L n : ℕ} (hnL : n ≤ L)
    {ω : ConfigSpace (Sym2 (Site 2))} {x₁ x₂ x₃ : Site 2}
    (hb₁ : x₁ ∈ box 2 n) (hb₂ : x₂ ∈ box 2 n) (hb₃ : x₃ ∈ box 2 n)
    (hi₁ : (cluster 2 ω x₁).Infinite) (hi₂ : (cluster 2 ω x₂).Infinite)
    (hi₃ : (cluster 2 ω x₃).Infinite)
    (hd₁₂ : cluster 2 ω x₁ ≠ cluster 2 ω x₂) (hd₁₃ : cluster 2 ω x₁ ≠ cluster 2 ω x₃)
    (hd₂₃ : cluster 2 ω x₂ ≠ cluster 2 ω x₃) :
    bc61_IsCoarseTrifurcation ω L 0 :=
  bc119_merge_at_y hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
    ⟨x₁, bkm_box_subset_boxAround hnL hb₁, rfl⟩
    ⟨x₂, bkm_box_subset_boxAround hnL hb₂, rfl⟩
    ⟨x₃, bkm_box_subset_boxAround hnL hb₃, rfl⟩

lemma bkm_recenterBoxMerge_of_le {L n : ℕ} (hnL : n ≤ L) :
    bc119_RecenterBoxMerge 2 L n := by
  intro ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  refine ⟨0, ∅, ?_⟩
  rw [Percolation.DisjointPaths.mng_forceOpenFinset_empty]
  exact bkm_coarseTrif_of_le hnL hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃

lemma bkm_recenterBoxMerge_diag (n : ℕ) : bc119_RecenterBoxMerge 2 n n :=
  bkm_recenterBoxMerge_of_le (le_refl n)

/-! ## B. The coarse step -/

lemma bkm_coarseTrifExistence_diag
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤}) :
    ∃ L : ℕ, 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
  obtain ⟨n, hnpos⟩ := exists_threeMeetBox_pos μ htop
  exact ⟨n, bc119_originCoarseTrif_at_of_residue μ hinv hfe (bkm_recenterBoxMerge_diag n) hnpos⟩

lemma bkm_coarseTrifExistence_atSomeScale
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤}) :
    ∃ L : ℕ, bc61_CoarseTrifExistence μ L := by
  obtain ⟨L, hL⟩ := bkm_coarseTrifExistence_diag μ hinv hfe htop
  exact ⟨L, fun _ => hL⟩

lemma bkm_status :
    (∀ (L n : ℕ), n ≤ L → bc119_RecenterBoxMerge 2 L n) ∧
    (∀ (n : ℕ), bc119_RecenterBoxMerge 2 n n) ∧
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ →
      0 < μ {ω | numInfiniteClusters 2 ω = ⊤} →
      ∃ L : ℕ, bc61_CoarseTrifExistence μ L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L n hnL; exact bkm_recenterBoxMerge_of_le hnL
  · intro n; exact bkm_recenterBoxMerge_diag n
  · intro μ _ hinv hfe htop; exact bkm_coarseTrifExistence_atSomeScale μ hinv hfe htop

end StatMech.Walls
