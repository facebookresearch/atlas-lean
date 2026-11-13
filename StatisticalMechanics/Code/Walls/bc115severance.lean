/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Walls.bc111routing

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
















theorem bc115_coarsePrecursor_of_coarseTrif (L : ℕ) {ω' : ConfigSpace (Sym2 (Site d))}
    (h : bc61_IsCoarseTrifurcation ω' L 0) :
    ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
      ω' ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃ := by
  obtain ⟨a₁, a₂, a₃, ⟨b₁, hb₁, hadj₁⟩, ⟨b₂, hb₂, hadj₂⟩, ⟨b₃, hb₃, hadj₃⟩,
    ⟨hinf₁, hinf₂, hinf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩ := h
  refine ⟨a₁, a₂, a₃, b₁, b₂, b₃, ⟨hb₁, hb₂, hb₃⟩, ⟨?_, ?_, ?_⟩,
    ⟨hinf₁, hinf₂, hinf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩
  · exact ((openSubgraph_adj (d := d) (ω := ω') b₁ a₁).mp hadj₁).1
  · exact ((openSubgraph_adj (d := d) (ω := ω') b₂ a₂).mp hadj₂).1
  · exact ((openSubgraph_adj (d := d) (ω := ω') b₃ a₃).mp hadj₃).1













theorem bc115_disconnected_of_distinctClusters (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hne : cluster d ω x ≠ cluster d ω y) :
    ¬ Connected d (removeSites T ω) x y := by
  intro hcut
  exact hne (cluster_eq_of_connected (connected_mono (daep_removeSites_le T ω) hcut))





theorem bc115_coarseTrif_disconnection_free (L : ℕ) {ω' : ConfigSpace (Sym2 (Site d))}
    (h : bc61_IsCoarseTrifurcation ω' L 0) :
    ∃ a₁ a₂ a₃ : Site d,
      ¬ Connected d (removeSites (bc61_boxAround d L 0) ω') a₁ a₂ ∧
      ¬ Connected d (removeSites (bc61_boxAround d L 0) ω') a₁ a₃ ∧
      ¬ Connected d (removeSites (bc61_boxAround d L 0) ω') a₂ a₃ := by
  obtain ⟨a₁, a₂, a₃, _, _, _, _, hcut₁₂, hcut₁₃, hcut₂₃⟩ := h
  exact ⟨a₁, a₂, a₃, hcut₁₂, hcut₁₃, hcut₂₃⟩












def bc115_CoarseTrifMerge (d L n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∀ x₁ x₂ x₃ : Site d,
    x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
    (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
    cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
    cluster d ω x₂ ≠ cluster d ω x₃ →
    ∃ W : Finset (Sym2 (Site d)),
      bc61_IsCoarseTrifurcation (forceOpenFinset W ω) L 0





theorem bc115_coarseBoxAttach_of_merge {L n : ℕ} (hmerge : bc115_CoarseTrifMerge d L n) :
    bc111_CoarseBoxAttach d L n := by
  intro ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  obtain ⟨W, htrif⟩ := hmerge ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hmem⟩ := bc115_coarsePrecursor_of_coarseTrif L htrif
  exact ⟨a₁, a₂, a₃, b₁, b₂, b₃, W, hmem⟩












theorem bc115_hcoarseRoute_of_merge
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ) (hmerge : ∀ n : ℕ, bc115_CoarseTrifMerge d L n) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) :=
  bc111_hcoarseRoute_of_coarseAttach μ hfe L (fun n => bc115_coarseBoxAttach_of_merge (hmerge n))





theorem bc115_coarseTrifExistence_of_merge
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ) (hmerge : ∀ n : ℕ, bc115_CoarseTrifMerge d L n) :
    bc61_CoarseTrifExistence μ L :=
  bc111_coarseTrifExistence_of_coarseAttach μ hfe L
    (fun n => bc115_coarseBoxAttach_of_merge (hmerge n))










theorem bc115_forceOpen_empty (ω : ConfigSpace (Sym2 (Site d))) :
    forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
  funext e; simp [forceOpenFinset]






theorem bc115_merge_upperLines_emptyWiring {L : ℕ} (hL : 3 ≤ L) :
    ∃ W : Finset (Sym2 (Site 2)),
      bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) L 0 := by
  refine ⟨∅, ?_⟩
  rw [bc115_forceOpen_empty]
  exact bc61_wholeBox_severs_upperLines hL





theorem bc115_precursor_upperLines_via_merge {L : ℕ} (hL : 3 ≤ L) :
    ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2) (W : Finset (Sym2 (Site 2))),
      forceOpenFinset W bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃ := by
  obtain ⟨W, htrif⟩ := bc115_merge_upperLines_emptyWiring hL
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hmem⟩ := bc115_coarsePrecursor_of_coarseTrif L htrif
  exact ⟨a₁, a₂, a₃, b₁, b₂, b₃, W, hmem⟩




































theorem bc115_status :
    
    (∀ (L : ℕ) (ω' : ConfigSpace (Sym2 (Site d))), bc61_IsCoarseTrifurcation ω' L 0 →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, ω' ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) ∧
    
    (∀ (L n : ℕ), bc115_CoarseTrifMerge d L n → bc111_CoarseBoxAttach d L n) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      HasFiniteEnergyMerge μ → (∀ n : ℕ, bc115_CoarseTrifMerge 2 L n) →
      (0 < μ {ω | numInfiniteClusters 2 ω = ⊤} →
        ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site 2,
          0 < μ (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃))
      ∧ bc61_CoarseTrifExistence μ L) ∧
    
    (∀ (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d),
      cluster d ω x ≠ cluster d ω y → ¬ Connected d (removeSites T ω) x y) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      ∃ W : Finset (Sym2 (Site 2)), bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) L 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro L ω' h; exact bc115_coarsePrecursor_of_coarseTrif L h
  · intro L n hmerge; exact bc115_coarseBoxAttach_of_merge hmerge
  · intro μ _ L hfe hmerge
    exact ⟨bc115_hcoarseRoute_of_merge μ hfe L hmerge, bc115_coarseTrifExistence_of_merge μ hfe L hmerge⟩
  · intro T ω x y hne; exact bc115_disconnected_of_distinctClusters T ω hne
  · intro L hL; exact bc115_merge_upperLines_emptyWiring hL

end StatMech.Walls
