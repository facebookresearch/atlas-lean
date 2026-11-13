/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Walls.bc102armleafboundary
import Code.Walls.bc94density
import Code.Walls.bc55route
import Code.Walls.bc56menger
import Code.Walls.bc99connect

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




















theorem bc104_bk_uniqueness_of_boxMenger (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hattach : ∀ n : ℕ, bmm_BoxMengerAttachment d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc55_burton_keane_bernoulli_of_boxMenger hd p hp1 hp0 hattach





theorem bc104_dc_step1_uniqueness (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc85_dc_step1_uniqueness μ hd L herg hfe hinv hforest_ae hexist hmergeGeom



theorem bc104_dc_bootstrap (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc85_dc_bootstrap μ hd L hinv hforest_ae hexist




theorem bc104_badBox_forces_two (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y' : Site d}
    (h : bc93_BadBox ω L y') : 2 ≤ numInfiniteClusters d ω :=
  bc93_two_le_numInfinite_of_badBox ω L h






theorem bc104_count_bound_under_top (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hN : numInfiniteClusters d ω = ⊤) (h : bst_BoxOpenForest ω n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  bc94_count_bound_under_top ω n hN h






theorem bc104_coarse_count_from_connectedForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc102_count_forest_derivable ω L R h







theorem bc104_complete_chain (hd : 1 ≤ d) :
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ n : ℕ, bmm_BoxMengerAttachment d n) →
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsErgodic (G := Multiplicative (Site d)) μ → HasFiniteEnergyMerge μ →
      IsTranslationInvariant (G := Multiplicative (Site d)) μ →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L →
      (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
        ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) →
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y' : Site d),
      bc93_BadBox ω L y' → 2 ≤ numInfiniteClusters d ω) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), numInfiniteClusters d ω = ⊤ →
      bst_BoxOpenForest ω n → bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp1 hp0 hattach
    exact (bc104_bk_uniqueness_of_boxMenger hd p hp1 hp0 hattach).2.2
  · intro μ _ L herg hfe hinv hforest_ae hexist hmergeGeom
    exact bc104_dc_step1_uniqueness μ hd L herg hfe hinv hforest_ae hexist hmergeGeom
  · intro ω L y' h; exact bc104_badBox_forces_two ω L h
  · intro ω n hN h; exact bc104_count_bound_under_top ω n hN h
  · intro ω L R h; exact bc104_coarse_count_from_connectedForest ω L R h











theorem bc104_bc56_refuted : ¬ bc56_BoxClusterReachesNbr 2 3 :=
  bc99_boxReachesNbr_fails




theorem bc104_bc56_notFree_of_coarseTrif {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ bc56_BoxClusterReachesNbr 2 3 :=
  bc99_notFree_of_coarseTrif hL







theorem bc104_bc64_refuted (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc102_bc64_crossSV_refuted L




theorem bc104_bc64_disjointStar_degrees :
    bc64_starG.degree 0 = 3 ∧ (∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1) :=
  bc102_bc64_disjointStar_degrees





theorem bc104_bc69_count_derivable (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc102_count_forest_derivable ω L R h







theorem bc104_residue_evolution :
    
    (¬ bc56_BoxClusterReachesNbr 2 3) ∧
    
    (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧
    
    (bc64_starG.degree 0 = 3 ∧ (∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨bc104_bc56_refuted, ?_, bc104_bc64_disjointStar_degrees, ?_⟩
  · intro L; exact bc104_bc64_refuted L
  · intro ω L R h; exact bc104_bc69_count_derivable ω L R h









theorem bc104_proved_dc_bootstrap (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc85_dc_bootstrap μ hd L hinv hforest_ae hexist






theorem bc104_proved_leaf_count {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  bc102_leaf_count_absorbs_shared G hacyc hmin





theorem bc104_proved_branch_le_leaf (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) :
    (bc80_branchFinset ω L R c S).card ≤ (bc80_leafFinset ω L R c S).card :=
  bc80_branch_le_leaf ω L R c S (fun v => by convert hmin v using 2)






theorem bc104_proved_leaf_boundary_free {p : Site d → Prop} (S : Set (Subtype p)) :
    Set.InjOn (Subtype.val : Subtype p → Site d) S :=
  bc102_leaf_boundary_free_on_subtype S





theorem bc104_proved_three_incident_arms (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
      ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
       (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
       (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :=
  bc101_gnTrif_three_incident_arms ω L y h





theorem bc104_proved_spanForest_exists (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
    (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
    bst_BoxOpenForest ω n :=
  bc90_boxOpenForest_of_genuine_armsInBox ω n hn hcanon harmbox hexists






theorem bc104_proved_fragments (hd : 1 ≤ d) :
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site d)) μ →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    
    (∀ (R : ℕ) (S : Set (↑(box d R) : Type)),
      Set.InjOn (Subtype.val : (↑(box d R) : Type) → Site d) S) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d), bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site d,
        (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
        (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
         ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
         ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro μ _ L hinv hforest_ae hexist; exact bc104_proved_dc_bootstrap μ hd L hinv hforest_ae hexist
  · intro V _ _ G _ hacyc hmin; exact bc104_proved_leaf_count G hacyc hmin
  · intro R S; exact bc104_proved_leaf_boundary_free S
  · intro ω L y h
    obtain ⟨a₁, a₂, a₃, hincs, _hinf, hcuts⟩ := bc104_proved_three_incident_arms ω L y h
    exact ⟨a₁, a₂, a₃, hincs, hcuts⟩









theorem bc104_refuted_singleSite : ¬ bc56_BoxClusterReachesNbr 2 3 :=
  bc99_boxReachesNbr_fails




theorem bc104_refuted_disjointStar (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc102_bc64_crossSV_refuted L





theorem bc104_refuted_straightAxis (j : Fin 2) :
    ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) j :=
  bc56_offAxisLine_no_runsAlongAxis j







theorem bc104_refuted_twoTerminalMenger (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc61_CoarseForestLeafCount ω L R :=
  bc101_residue_is_boundary_injection ω L R hz₀ hz₁ hzne hinj





theorem bc104_refuted_finiteN_conditioning (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] :
    μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc85_finiteN_iff_top_null μ






theorem bc104_refuted_routes :
    
    (¬ bc56_BoxClusterReachesNbr 2 3) ∧
    
    (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧
    
    (∀ j : Fin 2, ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) j) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ],
      μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨bc104_refuted_singleSite, ?_, ?_, ?_⟩
  · intro L; exact bc104_refuted_disjointStar L
  · intro j; exact bc104_refuted_straightAxis j
  · intro μ _; exact bc104_refuted_finiteN_conditioning μ














theorem bc104_residue_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc69_Gn_globalForest ω L R :=
  bc102_connectedForest_of_noTrif ω L R hz₀ hz₁ hzne hno














theorem bc104_residue_closes_bk
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc69_infiniteClusters_top_null_of_globalForest μ hd hinv hfe L hGlobal hcoarseRoute





theorem bc104_minimal_residue (hd : 1 ≤ d) :
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
      (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
      (hfe : HasFiniteEnergyMerge μ) (L : ℕ),
      (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R) →
      (0 < μ {ω | numInfiniteClusters d ω = ⊤} →
        ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
          0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) → bc69_Gn_globalForest ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ _ hinv hfe L hGlobal hcoarseRoute
    exact bc104_residue_closes_bk μ hd hinv hfe L hGlobal hcoarseRoute
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hno
    exact bc104_residue_nonvacuous ω L R hz₀ hz₁ hzne hno
  · intro ω L R h; exact bc104_coarse_count_from_connectedForest ω L R h



































theorem bc104_status (hd : 1 ≤ d) :
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ n : ℕ, bmm_BoxMengerAttachment d n) →
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site d)) μ →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    
    ((¬ bc56_BoxClusterReachesNbr 2 3) ∧
     (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
       Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧
     (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
        bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R)) ∧
    
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    
    ((∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
        (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
        (hfe : HasFiniteEnergyMerge μ) (L : ℕ),
        (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R) →
        (0 < μ {ω | numInfiniteClusters d ω = ⊤} →
          ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
            0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) →
        μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
     (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
        z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
        (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) → bc69_Gn_globalForest ω L R)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp1 hp0 hattach
    exact (bc104_bk_uniqueness_of_boxMenger hd p hp1 hp0 hattach).2.2
  · intro μ _ L hinv hforest_ae hexist; exact bc104_proved_dc_bootstrap μ hd L hinv hforest_ae hexist
  · exact ⟨bc104_bc56_refuted,
      fun L => bc104_bc64_refuted L, fun ω L R h => bc104_bc69_count_derivable ω L R h⟩
  · intro V _ _ G _ hacyc hmin; exact bc104_proved_leaf_count G hacyc hmin
  · refine ⟨?_, ?_⟩
    · intro μ _ hinv hfe L hGlobal hcoarseRoute
      exact bc104_residue_closes_bk μ hd hinv hfe L hGlobal hcoarseRoute
    · intro ω L R z₀ z₁ hz₀ hz₁ hzne hno
      exact bc104_residue_nonvacuous ω L R hz₀ hz₁ hzne hno

end StatMech.Walls
