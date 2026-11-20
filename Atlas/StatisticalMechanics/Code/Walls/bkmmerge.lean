/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Walls.bc119recenter

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}









theorem bkm_box_subset_boxAround {L n : ℕ} (hnL : n ≤ L) {x : Site 2} (hx : x ∈ box 2 n) :
    x ∈ bc61_boxAround 2 L 0 := by
  rw [bc61_mem_boxAround_zero]
  exact box_mono 2 hnL hx
















theorem bkm_coarseTrif_of_le {L n : ℕ} (hnL : n ≤ L)
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






theorem bkm_recenterBoxMerge_of_le {L n : ℕ} (hnL : n ≤ L) :
    bc119_RecenterBoxMerge 2 L n := by
  intro ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  refine ⟨0, ∅, ?_⟩
  rw [bc115_forceOpen_empty]
  exact bkm_coarseTrif_of_le hnL hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃






theorem bkm_recenterBoxMerge_diag (n : ℕ) : bc119_RecenterBoxMerge 2 n n :=
  bkm_recenterBoxMerge_of_le (le_refl n)
























theorem bkm_coarseTrifExistence_diag
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤}) :
    ∃ L : ℕ, 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
  obtain ⟨n, hnpos⟩ := exists_threeMeetBox_pos μ htop
  exact ⟨n, bc119_originCoarseTrif_at_of_residue μ hinv hfe (bkm_recenterBoxMerge_diag n) hnpos⟩






theorem bkm_coarseTrifExistence_atSomeScale
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤}) :
    ∃ L : ℕ, bc61_CoarseTrifExistence μ L := by
  obtain ⟨L, hL⟩ := bkm_coarseTrifExistence_diag μ hinv hfe htop
  exact ⟨L, fun _ => hL⟩


















































theorem bkm_status :
    
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
