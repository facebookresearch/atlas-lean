/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Walls.bc62coarseclose
import Code.Percolation.CanonForestCount

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}













theorem bc63_coarseArm_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z :=
  daep_infinite_reaches_boundary (removeSites (bc61_boxAround d L y) ω) R hR a habox hinf











theorem bc63_coarseForest_acyclic {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (osf_spanForest G).IsAcyclic :=
  osf_spanForest_acyclic G



theorem bc63_subgraph_acyclic {V : Type*} [Fintype V] (G T : SimpleGraph V)
    (hsub : T ≤ osf_spanForest G) : T.IsAcyclic :=
  (osf_spanForest_acyclic G).anti hsub










theorem bc63_coarseForestLeafCount_discharges_count (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc61_CoarseForestLeafCount ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc61_coarseTcount_le_boundary_of_forest ω L R h










open Classical in





theorem bc63_coarseForestLeafCount_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc61_IsCoarseTrifurcation ω L y) :
    bc61_CoarseForestLeafCount ω L R := by
  classical
  refine ⟨Fin 2, inferInstance, ⟨0⟩, inferInstance, Flc2Witness.pathG, inferInstance,
    (fun _ => (0 : Fin 2)), (fun v => if v = 0 then z₀ else z₁),
    Flc2Witness.pathG_isTree.isAcyclic, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro v; rw [Flc2Witness.pathG_deg v]
  · 
    intro y hybox htri; exact absurd htri (hno y hybox)
  · 
    intro y hybox htri z hzbox htriz _; exact absurd htri (hno y hybox)
  · 
    intro v _; fin_cases v
    · simpa using hz₀
    · simpa using hz₁
  · 
    intro u hu v hv huv
    fin_cases u <;> fin_cases v
    · rfl
    · exact absurd huv hzne
    · exact absurd huv.symm hzne
    · rfl

open Classical in






theorem bc63_coarseForestLeafCount_star (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {r : Site d} (_hrbox : r ∈ box d R) (_htri_r : bc61_IsCoarseTrifurcation ω L r)
    (z : Fin 3 → Site d) (hzb : ∀ i, z i ∈ vertexBoundary d R) (hzinj : Function.Injective z)
    (hsingle : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → y = r) :
    bc61_CoarseForestLeafCount ω L R := by
  classical
  set lamL : Fin 4 → Site d := fun v =>
    if v = 1 then z 0 else if v = 2 then z 1 else if v = 3 then z 2 else z 0 with hlamL
  refine ⟨Fin 4, inferInstance, ⟨0⟩, inferInstance, Flc2Witness.starG, inferInstance,
    (fun _ => (0 : Fin 4)), lamL, Flc2Witness.starG_isTree.isAcyclic, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro v
    by_cases hv : v = 0
    · rw [hv, Flc2Witness.starG_centre_deg]; omega
    · rw [Flc2Witness.starG_leaf_deg v hv]
  · 
    intro y hybox htri; rw [Flc2Witness.starG_centre_deg]
  · 
    intro y hybox htri z' hz'box htriz' _
    rw [hsingle y hybox htri, hsingle z' hz'box htriz']
  · 
    intro v hv
    rw [Flc2Witness.starG_deg1_iff] at hv
    fin_cases v
    · exact absurd rfl hv
    · simpa [hlamL] using hzb 0
    · simpa [hlamL] using hzb 1
    · simpa [hlamL] using hzb 2
  · 
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_filter] at hu hv
    rw [Flc2Witness.starG_deg1_iff] at hu hv
    have hu' := hu.2; have hv' := hv.2
    fin_cases u <;> fin_cases v <;>
      first
        | exact absurd rfl hu'
        | exact absurd rfl hv'
        | rfl
        | (revert huv; simp only [hlamL]; intro huv; exact absurd (hzinj huv) (by decide))

















def bc63_CoarseArmEmbedding (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  bc61_CoarseForestLeafCount ω L R





theorem bc63_coarseArmEmbedding_iff_forestLeafCount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc63_CoarseArmEmbedding ω L R ↔ bc61_CoarseForestLeafCount ω L R :=
  Iff.rfl






theorem bc63_coarseForestLeafCount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc63_CoarseArmEmbedding ω L R) : bc61_CoarseForestLeafCount ω L R :=
  (bc63_coarseArmEmbedding_iff_forestLeafCount ω L R).mp h



theorem bc63_coarseTcount_le_boundary_of_armEmbedding (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc63_CoarseArmEmbedding ω L R) : bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc63_coarseForestLeafCount_discharges_count ω L R (bc63_coarseForestLeafCount ω L R h)





theorem bc63_coarseArmEmbedding_star (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {r : Site d} (hrbox : r ∈ box d R) (htri_r : bc61_IsCoarseTrifurcation ω L r)
    (z : Fin 3 → Site d) (hzb : ∀ i, z i ∈ vertexBoundary d R) (hzinj : Function.Injective z)
    (hsingle : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → y = r) :
    bc63_CoarseArmEmbedding ω L R :=
  bc63_coarseForestLeafCount_star ω L R hrbox htri_r z hzb hzinj hsingle

























theorem bc63_coarseRoute_of_precursor_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (hpre : 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) :=
  fun _ => ⟨a₁, a₂, a₃, b₁, b₂, b₃, hpre⟩






theorem bc63_coarseTrifExistence_of_precursor_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (hpre : 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bc61_CoarseTrifExistence μ L :=
  bc62_coarseTrifExistence_of_route μ hfe L
    (bc63_coarseRoute_of_precursor_pos μ L a₁ a₂ a₃ b₁ b₂ b₃ hpre)
















theorem bc63_upperLines_arm_reaches_boundary {L R : ℕ} (hR : 1 ≤ R) {h : ℤ} (hh : 1 ≤ h)
    (hbox : bc57_pt ((L : ℤ) + 1) h ∈ box 2 R) :
    ∃ z ∈ vertexBoundary 2 R,
      Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
        (bc57_pt ((L : ℤ) + 1) h) z :=
  bc63_coarseArm_reaches_boundary bc60_upperLines L R hR 0 (bc57_pt ((L : ℤ) + 1) h) hbox
    (bc61_upperLines_rightArm_infinite hh)







theorem bc63_upperLines_coarsePrecursor_nonempty {L : ℕ} (hL : 3 ≤ L) :
    bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L
      (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3)
      (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3) :=
  bc62_upperLines_mem_coarsePrecursor hL







theorem bc63_upperLines_coarseTrifExistence
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) {L : ℕ}
    (hpre : 0 < μ (bc62_CoarseTrifPrecursor 2 L
      (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3)
      (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3))) :
    bc61_CoarseTrifExistence μ L :=
  bc63_coarseTrifExistence_of_precursor_pos μ hfe L _ _ _ _ _ _ hpre

























theorem bc63_infiniteClusters_top_null_of_armEmbedding_route
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (harm : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc63_CoarseArmEmbedding ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc62_infiniteClusters_top_null_of_forest_route μ hd hinv hfe L
    (fun ω R => bc63_coarseForestLeafCount ω L R (harm ω R)) hcoarseRoute



























theorem bc63_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z) ∧
    
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (osf_spanForest G).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc63_CoarseArmEmbedding ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3)
        (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3)) :=
  ⟨fun ω L R hR y a habox hinf => bc63_coarseArm_reaches_boundary ω L R hR y a habox hinf,
   fun G => bc63_coarseForest_acyclic G,
   fun ω L R h => bc63_coarseTcount_le_boundary_of_armEmbedding ω L R h,
   fun hL => bc63_upperLines_coarsePrecursor_nonempty hL⟩

end StatMech.Walls
