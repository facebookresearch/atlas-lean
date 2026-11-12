/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Walls.bc94density
import Code.Percolation.BurtonKeaneMerge

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}















theorem bc95_spanForest_exists {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧ (∀ {u v : V}, G.Reachable u v → F.Reachable u v) :=
  ⟨osf_spanForest G, osf_spanForest_le G, osf_spanForest_acyclic G,
    fun {u v} h => osf_spanForest_reachable_of G h⟩





theorem bc95_spanForest_degree_pos {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel (osf_spanForest G).Adj] {u v : V} (hv : v ≠ u) (h : G.Reachable u v) :
    1 ≤ (osf_spanForest G).degree u :=
  osf_spanForest_degree_pos_of_reachable_ne G hv h


















theorem bc95_boxOpenForest_of_harmbox (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
    (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
    bst_BoxOpenForest ω n :=
  bc90_boxOpenForest_of_genuine_armsInBox ω n hn hcanon harmbox hexists


















def bc95_AeArmReaching (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) ∧
    (∃ x, x ∈ box d n ∧ IsTrifurcation d ω x)





theorem bc95_ae_genuineCount_of_armReaching (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hres : bc95_AeArmReaching μ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
  filter_upwards [hres n hn] with ω hω
  obtain ⟨hcanon, harmbox, _⟩ := hω
  exact bc90_genuineTcount_le_boundary_of_genuine_armsInBox ω n hn hcanon harmbox











theorem bc95_forestResidue_of_ae_armReaching (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hres : bc95_AeArmReaching μ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, bst_BoxOpenForest ω n := by
  filter_upwards [hres n hn] with ω hω
  obtain ⟨hcanon, harmbox, hexists⟩ := hω
  exact bc95_boxOpenForest_of_harmbox ω n hn hcanon harmbox hexists




















def bc95_SingleSiteRewiring (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  0 < μ {ω | numInfiniteClusters d ω = ⊤} →
    ∃ A : Set (ConfigSpace (Sym2 (Site d))),
      0 < μ A ∧ A ⊆ {ω | bc89_GenuineTrif d ω 0}





theorem bc95_density_of_singleSiteRewiring (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hrw : bc95_SingleSiteRewiring μ) : bc94_GenuineTrifExistence μ := by
  intro hpos
  obtain ⟨A, hApos, hAsub⟩ := hrw hpos
  exact lt_of_lt_of_le hApos (measure_mono hAsub)






theorem bc95_bk_from_residues (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
    (hrw : bc95_SingleSiteRewiring μ) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc94_bk_from_density μ hprob0 (bc95_density_of_singleSiteRewiring μ hrw)















theorem bc95_perConfig_contrast {V : Type*} [Fintype V] (G : SimpleGraph V)
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) :
    
    (∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧ (∀ {u v : V}, G.Reachable u v → F.Reachable u v)) ∧
    
    ((∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x) →
     (∀ x, x ∈ box d n → IsTrifurcation d ω x →
       ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) →
     (∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) →
     bst_BoxOpenForest ω n) := by
  refine ⟨bc95_spanForest_exists G, ?_⟩
  intro hcanon harmbox hexists
  exact bc95_boxOpenForest_of_harmbox ω n hn hcanon harmbox hexists












theorem bc95_upperLines_zero_density (n : ℕ) :
    bc89_genuineTcount bc60_upperLines n = 0 ∧
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  ⟨bc89_upperLines_genuineTcount_zero n, bc85_upperLines_N_top⟩


































theorem bc95_status :
    
    (∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
        (∀ {u v : V}, G.Reachable u v → F.Reachable u v)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x →
        ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) →
      (∃ x, x ∈ box 2 n ∧ IsTrifurcation 2 ω x) →
      bst_BoxOpenForest ω n) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))), bc95_AeArmReaching μ →
      ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, bst_BoxOpenForest ω n) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))), bc95_SingleSiteRewiring μ →
      bc94_GenuineTrifExistence μ) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      μ {ω | bc89_GenuineTrif 2 ω 0} = 0 → bc95_SingleSiteRewiring μ →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (∀ n : ℕ, bc89_genuineTcount bc60_upperLines n = 0 ∧
      numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro V _ G; exact bc95_spanForest_exists G
  · intro ω n hn hcanon harmbox hexists; exact bc95_boxOpenForest_of_harmbox ω n hn hcanon harmbox hexists
  · intro μ hres n hn; exact bc95_forestResidue_of_ae_armReaching μ hres n hn
  · intro μ hrw; exact bc95_density_of_singleSiteRewiring μ hrw
  · intro μ _ hprob0 hrw; exact bc95_bk_from_residues μ hprob0 hrw
  · intro n; exact bc95_upperLines_zero_density n

end StatMech.Walls
