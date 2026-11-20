/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Walls.bc62coarseclose
import Code.Walls.bc61coarsebox
import Code.Percolation.TrifurcationConstruction
import Code.Percolation.HrouteDisjointPaths

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














theorem bc111_measurableSet_coarsePrecursor (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d) :
    MeasurableSet (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) := by
  classical
  set T : Finset (Site d) := bc61_boxAround d L 0 with hT
  
  set guard : Prop :=
    (b₁ ∈ T ∧ b₂ ∈ T ∧ b₃ ∈ T) ∧
    ((hypercubicLattice d).Adj b₁ a₁ ∧ (hypercubicLattice d).Adj b₂ a₂ ∧
      (hypercubicLattice d).Adj b₃ a₃) with hguard
  have heq : bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃
      = (if guard then Set.univ else ∅)
          ∩ ({ω | (cluster d (removeSites T ω) a₁).Infinite} ∩
              {ω | (cluster d (removeSites T ω) a₂).Infinite} ∩
              {ω | (cluster d (removeSites T ω) a₃).Infinite})
          ∩ ({ω | ¬ Connected d (removeSites T ω) a₁ a₂} ∩
              {ω | ¬ Connected d (removeSites T ω) a₁ a₃} ∩
              {ω | ¬ Connected d (removeSites T ω) a₂ a₃}) := by
    ext ω
    simp only [bc62_CoarseTrifPrecursor, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hb1, hb2, hb3⟩, ⟨hadj1, hadj2, hadj3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩
      refine ⟨⟨?_, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs12, hs13⟩, hs23⟩⟩
      rw [if_pos ⟨⟨hb1, hb2, hb3⟩, ⟨hadj1, hadj2, hadj3⟩⟩]; exact Set.mem_univ _
    · rintro ⟨⟨hif, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs12, hs13⟩, hs23⟩⟩
      by_cases hg : guard
      · obtain ⟨⟨hb1, hb2, hb3⟩, ⟨hadj1, hadj2, hadj3⟩⟩ := hg
        exact ⟨⟨hb1, hb2, hb3⟩, ⟨hadj1, hadj2, hadj3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩
      · rw [if_neg hg] at hif; exact absurd hif (Set.notMem_empty _)
  rw [heq]
  apply MeasurableSet.inter
  apply MeasurableSet.inter
  · by_cases hg : guard
    · rw [if_pos hg]; exact MeasurableSet.univ
    · rw [if_neg hg]; exact MeasurableSet.empty
  · exact ((bc62_measurableSet_clusterInfinite_removeSites T a₁).inter
      (bc62_measurableSet_clusterInfinite_removeSites T a₂)).inter
      (bc62_measurableSet_clusterInfinite_removeSites T a₃)
  · exact (((bc62_measurableSet_connected_removeSites T a₁ a₂).compl).inter
      ((bc62_measurableSet_connected_removeSites T a₁ a₃).compl)).inter
      ((bc62_measurableSet_connected_removeSites T a₂ a₃).compl)

















def bc111_CoarseBoxAttach (d L n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∀ x₁ x₂ x₃ : Site d,
    x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
    (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
    cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
    cluster d ω x₂ ≠ cluster d ω x₃ →
    ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site d) (W : Finset (Sym2 (Site d))),
      forceOpenFinset W ω ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃








theorem bc111_coarseBoxRoute_of_attach {L n : ℕ} (hres : bc111_CoarseBoxAttach d L n)
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site d) (W : Finset (Sym2 (Site d))),
      forceOpenFinset W ω ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃ := by
  obtain ⟨x₁, x₂, x₃, ⟨hb1, hb2, hb3⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ :=
    tfe_three_distinct_infinite_of_box hω
  exact hres ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hd12 hd13 hd23




theorem bc111_precursorCover_of_attach {L n : ℕ} (hres : bc111_CoarseBoxAttach d L n) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (b₁ : Site d) (b₂ : Site d) (b₃ : Site d)
        (W : Finset (Sym2 (Site d))),
        (fun ω => forceOpenFinset W ω) ⁻¹' bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃ := by
  intro ω hω
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, W, hmem⟩ := bc111_coarseBoxRoute_of_attach hres hω
  simp only [Set.mem_iUnion, Set.mem_preimage]
  exact ⟨a₁, a₂, a₃, b₁, b₂, b₃, W, hmem⟩










theorem bc111_hcoarseRoute_at_of_attach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) {L n : ℕ} (hres : bc111_CoarseBoxAttach d L n)
    (hpos : 0 < μ (threeMeetBox d n)) :
    ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
      0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) := by
  classical
  set ι := Site d × Site d × Site d × Site d × Site d × Site d × Finset (Sym2 (Site d)) with hι
  set B : ι → Set (ConfigSpace (Sym2 (Site d))) :=
    fun p => (fun ω => forceOpenFinset p.2.2.2.2.2.2 ω) ⁻¹'
      bc62_CoarseTrifPrecursor d L p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 with hB
  have hcover : threeMeetBox d n ⊆ ⋃ p : ι, B p := by
    intro ω hω
    obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, W, hmem⟩ := by
      have := bc111_precursorCover_of_attach hres hω
      simpa only [Set.mem_iUnion] using this
    exact Set.mem_iUnion.mpr ⟨(a₁, a₂, a₃, b₁, b₂, b₃, W), hmem⟩
  obtain ⟨p, hppos⟩ := DisjointPaths.exists_pos_of_cover μ hcover hpos
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, W⟩ := p
  refine ⟨a₁, a₂, a₃, b₁, b₂, b₃, ?_⟩
  exact DisjointPaths.pos_of_forceOpen_preimage μ hfe W
    (bc111_measurableSet_coarsePrecursor L a₁ a₂ a₃ b₁ b₂ b₃)
    (subset_rfl) hppos










theorem bc111_hcoarseRoute_of_coarseAttach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ) (hres : ∀ n : ℕ, bc111_CoarseBoxAttach d L n) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) := by
  intro hpos
  obtain ⟨n, hnpos⟩ := exists_threeMeetBox_pos μ hpos
  exact bc111_hcoarseRoute_at_of_attach μ hfe (hres n) hnpos









theorem bc111_coarseTrifExistence_of_coarseAttach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ) (hres : ∀ n : ℕ, bc111_CoarseBoxAttach d L n) :
    bc61_CoarseTrifExistence μ L :=
  bc62_coarseTrifExistence_of_route μ hfe L (bc111_hcoarseRoute_of_coarseAttach μ hfe L hres)














theorem bc111_coarsePrecursor_upperLines_emptyWiring {L : ℕ} (hL : 3 ≤ L) :
    forceOpenFinset (∅ : Finset (Sym2 (Site 2))) bc60_upperLines ∈
      bc62_CoarseTrifPrecursor 2 L
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3)
        (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3) := by
  have hforce : forceOpenFinset (∅ : Finset (Sym2 (Site 2))) bc60_upperLines = bc60_upperLines := by
    funext e; simp [forceOpenFinset]
  rw [hforce]
  exact bc62_upperLines_mem_coarsePrecursor hL





theorem bc111_coarseBoxRoute_upperLines_witness {L : ℕ} (hL : 3 ≤ L) :
    ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2) (W : Finset (Sym2 (Site 2))),
      forceOpenFinset W bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃ :=
  ⟨_, _, _, _, _, _, ∅, bc111_coarsePrecursor_upperLines_emptyWiring hL⟩













theorem bc111_coarsePrecursor_forces_boxAdjacency (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) :
    (b₁ ∈ bc61_boxAround d L 0 ∧ (hypercubicLattice d).Adj b₁ a₁) ∧
    (b₂ ∈ bc61_boxAround d L 0 ∧ (hypercubicLattice d).Adj b₂ a₂) ∧
    (b₃ ∈ bc61_boxAround d L 0 ∧ (hypercubicLattice d).Adj b₃ a₃) := by
  obtain ⟨⟨hb1, hb2, hb3⟩, ⟨hadj1, hadj2, hadj3⟩, _, _⟩ := hω
  exact ⟨⟨hb1, hadj1⟩, ⟨hb2, hadj2⟩, ⟨hb3, hadj3⟩⟩






































theorem bc111_status :
    
    (∀ (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2),
      MeasurableSet (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃)) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      HasFiniteEnergyMerge μ → (∀ n : ℕ, bc111_CoarseBoxAttach 2 L n) →
      0 < μ {ω | numInfiniteClusters 2 ω = ⊤} →
        ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site 2,
          0 < μ (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃)) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      HasFiniteEnergyMerge μ → (∀ n : ℕ, bc111_CoarseBoxAttach 2 L n) →
      bc61_CoarseTrifExistence μ L) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2) (W : Finset (Sym2 (Site 2))),
        forceOpenFinset W bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L a₁ a₂ a₃ b₁ b₂ b₃; exact bc111_measurableSet_coarsePrecursor L a₁ a₂ a₃ b₁ b₂ b₃
  · intro μ _ L hfe hres hpos; exact bc111_hcoarseRoute_of_coarseAttach μ hfe L hres hpos
  · intro μ _ L hfe hres; exact bc111_coarseTrifExistence_of_coarseAttach μ hfe L hres
  · intro L hL; exact bc111_coarseBoxRoute_upperLines_witness hL

end StatMech.Walls
