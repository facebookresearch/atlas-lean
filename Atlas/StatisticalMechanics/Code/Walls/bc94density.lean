/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































































import Mathlib
import Code.Walls.bc93badbox
import Code.Walls.bc90boxopenforest
import Code.Walls.bc89genuinetrifae

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

















def bc94_GenuineTrifExistence (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  0 < μ {ω | numInfiniteClusters d ω = ⊤} →
    0 < μ {ω | bc89_GenuineTrif d ω 0}














theorem bc94_genuineTcount_le_boundary_of_forest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bst_BoxOpenForest ω n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  bc89_genuineTcount_le_boundary_of_openForest ω n h







theorem bc94_genuineTcount_le_boundary_of_inputs (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  bc90_genuineTcount_le_boundary_of_genuine_armsInBox ω n hn hcanon harmbox














theorem bc94_count_bound_under_top (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (_hN : numInfiniteClusters d ω = ⊤) (h : bst_BoxOpenForest ω n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  bc94_genuineTcount_le_boundary_of_forest ω n h





theorem bc94_count_bound_under_ge_two (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (_hN : 2 ≤ numInfiniteClusters d ω)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  bc94_genuineTcount_le_boundary_of_inputs ω n hn hcanon harmbox












def bc94_DensityForestResidue (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ n : ℕ, ∀ᵐ ω ∂μ, bst_BoxOpenForest ω n




theorem bc94_ae_genuineCount_bound_of_residue (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hres : bc94_DensityForestResidue μ) (n : ℕ) :
    ∀ᵐ ω ∂μ, bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
  filter_upwards [hres n] with ω hω
  exact bc94_genuineTcount_le_boundary_of_forest ω n hω

















theorem bc94_upperLines_zero_density_and_N_top (n : ℕ) :
    bc89_genuineTcount bc60_upperLines n = 0 ∧
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  ⟨bc89_upperLines_genuineTcount_zero n, bc85_upperLines_N_top⟩












theorem bc94_forward_density_uses_top (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hexist : bc94_GenuineTrifExistence μ)
    (hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤}) :
    0 < μ {ω | bc89_GenuineTrif d ω 0} :=
  hexist hpos


















theorem bc94_exclude_top_of_density (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
    (hexist : bc94_GenuineTrifExistence μ) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  by_contra htop
  have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr htop
  have := hexist hpos
  rw [hprob0] at this
  exact lt_irrefl 0 this















theorem bc94_bk_from_density (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
    (hexist : bc94_GenuineTrifExistence μ) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc94_exclude_top_of_density μ hprob0 hexist


















theorem bc94_circularity_contrast (ω : ConfigSpace (Sym2 (Site d))) (L n : ℕ) :
    
    ((numInfiniteClusters d ω ≤ 1 → ∀ y', ¬ bc93_BadBox ω L y') ∧
     (∀ y', bc93_BadBox ω L y' → 2 ≤ numInfiniteClusters d ω)) ∧
    
    (numInfiniteClusters d ω = ⊤ → bst_BoxOpenForest ω n →
      bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n) := by
  refine ⟨⟨fun hN y' => bc93_no_badBox_of_le_one ω L hN y', ?_⟩, ?_⟩
  · intro y' h; exact bc93_two_le_numInfinite_of_badBox ω L h
  · intro hN h; exact bc94_count_bound_under_top ω n hN h









































theorem bc94_status :
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))), bc94_GenuineTrifExistence μ →
      0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → 0 < μ {ω | bc89_GenuineTrif 2 ω 0}) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), numInfiniteClusters 2 ω = ⊤ →
      bst_BoxOpenForest ω n → bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x →
        ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) →
      bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      μ {ω | bc89_GenuineTrif 2 ω 0} = 0 → bc94_GenuineTrifExistence μ →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L n : ℕ),
      ((numInfiniteClusters 2 ω ≤ 1 → ∀ y', ¬ bc93_BadBox ω L y') ∧
       (∀ y', bc93_BadBox ω L y' → 2 ≤ numInfiniteClusters 2 ω)) ∧
      (numInfiniteClusters 2 ω = ⊤ → bst_BoxOpenForest ω n →
        bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n)) ∧
    
    (∀ n : ℕ, bc89_genuineTcount bc60_upperLines n = 0 ∧
      numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ hexist hpos; exact bc94_forward_density_uses_top μ hexist hpos
  · intro ω n hN h; exact bc94_count_bound_under_top ω n hN h
  · intro ω n hn hcanon harmbox; exact bc94_genuineTcount_le_boundary_of_inputs ω n hn hcanon harmbox
  · intro μ _ hprob0 hexist; exact bc94_bk_from_density μ hprob0 hexist
  · intro ω L n; exact bc94_circularity_contrast ω L n
  · intro n; exact bc94_upperLines_zero_density_and_N_top n

end StatMech.Walls
