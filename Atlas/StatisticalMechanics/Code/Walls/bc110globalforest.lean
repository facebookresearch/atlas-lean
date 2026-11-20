/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Walls.bc103contractdeg
import Code.Walls.bc108sublatticeforest
import Code.Walls.bc107harmbox

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










theorem bc110_globalForest_of_contracted (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc103_ContractedTrifGraph ω L R) : bc69_Gn_globalForest ω L R :=
  bc103_globalForest_of_contractedGraph ω L R h





























theorem bc110_globalForest_all_free_except_contraction (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc103_ContractedTrifGraph ω L R) :
    bc69_Gn_globalForest ω L R ∧
    
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (osf_spanForest G).IsAcyclic) ∧
    
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel (osf_spanForest G).Adj]
      {u v₁ v₂ v₃ : V}, G.Adj u v₁ → G.Adj u v₂ → G.Adj u v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ →
      3 ≤ (osf_spanForest G).degree u) := by
  refine ⟨bc110_globalForest_of_contracted ω L R h, ?_, ?_⟩
  · intro V _ G; exact osf_spanForest_acyclic G
  · intro V _ G _ u v₁ v₂ v₃ h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
    exact bc103_deg3_spanForest_of_noBypass G h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃

















theorem bc110_contractionArm_of_trif (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (h : bc67_IsGnTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
      ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
       (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
       (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :=
  h




theorem bc110_contractionArm_of_coarseTrif (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (h : bc61_IsCoarseTrifurcation ω L y) :
    bc67_IsGnTrifurcation ω L y :=
  bc67_gnTrif_of_coarseTrif ω L y h











theorem bc110_globalForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc69_Gn_globalForest ω L R :=
  bc69_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno

open Classical in






theorem bc110_contractedGraph_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc103_ContractedTrifGraph ω L R := by
  classical
  
  set S : Set (Site d) := {z₀, z₁} with hS
  have hz₀S : z₀ ∈ S := by rw [hS]; left; rfl
  have hz₁S : z₁ ∈ S := by rw [hS]; right; rfl
  haveI hSfin : Fintype (↑S : Type) := (Set.toFinite S).fintype
  set a : (↑S : Type) := ⟨z₀, hz₀S⟩ with ha
  set b : (↑S : Type) := ⟨z₁, hz₁S⟩ with hb
  have hab : a ≠ b := fun h => hzne (congrArg Subtype.val h)
  let G : SimpleGraph (↑S : Type) := SimpleGraph.fromEdgeSet {s(a, b)}
  haveI hGdec : DecidableRel G.Adj := Classical.decRel _
  haveI hFdec : DecidableRel (osf_spanForest G).Adj := Classical.decRel _
  have hVall : ∀ v : (↑S : Type), v = a ∨ v = b := by
    intro v; obtain ⟨x, hx⟩ := v
    rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · left; rfl
    · right; rfl
  
  
  
  
  
  have hGac : G.IsAcyclic := bc69_single_edge_acyclic a b hab
  have hFeqG : osf_spanForest G = G := by
    
    have hspec := osf_spanForest_spec G
    have hle : G ≤ osf_spanForest G := hspec.2 ⟨le_refl G, hGac⟩ (osf_spanForest_le G)
    exact le_antisymm (osf_spanForest_le G) hle
  
  have hdeg_eq : ∀ v : (↑S : Type), (osf_spanForest G).degree v = G.degree v := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    rw [hFeqG]
  have hda : (osf_spanForest G).degree a = 1 := by
    rw [hdeg_eq a]; exact bc69_single_edge_degree a b hab
  have hdb : (osf_spanForest G).degree b = 1 := by
    rw [hdeg_eq b]; exact bc69_single_edge_degree_b a b hab
  refine ⟨S, hSfin, ⟨a⟩, G, hGdec, hFdec, (fun _ => a), ?_, ?_, ?_, ?_⟩
  · 
    intro y hybox htri; exact absurd htri (hno y hybox)
  · 
    intro v; rcases hVall v with rfl | rfl
    · rw [hda]
    · rw [hdb]
  · 
    intro y hybox htri; exact absurd htri (hno y hybox)
  · 
    intro v _; rcases hVall v with rfl | rfl
    · exact hz₀
    · exact hz₁




theorem bc110_globalForest_of_noTrif_via_contraction (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc69_Gn_globalForest ω L R :=
  bc110_globalForest_of_contracted ω L R
    (bc110_contractedGraph_of_noTrif ω L R hz₀ hz₁ hzne hno)






theorem bc110_count_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc69_count_via_leafBound ω L R h







theorem bc110_bk_count_half_closes_of_globalForest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc69_infiniteClusters_top_null_of_globalForest μ hd hinv hfe L hGlobal hcoarseRoute








































theorem bc110_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc103_ContractedTrifGraph ω L R → bc69_Gn_globalForest ω L R) ∧
    
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel (osf_spanForest G).Adj]
      (u v₁ v₂ v₃ : V), G.Adj u v₁ → G.Adj u v₂ → G.Adj u v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ →
      3 ≤ (osf_spanForest G).degree u) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d),
      bc67_IsGnTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site d,
        (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
         ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
         ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R h; exact bc110_globalForest_of_contracted ω L R h
  · intro V _ G _ u v₁ v₂ v₃ h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
    exact bc103_deg3_spanForest_of_noBypass G h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
  · intro ω L y h
    obtain ⟨a₁, a₂, a₃, _, _, hcut⟩ := h
    exact ⟨a₁, a₂, a₃, hcut⟩
  · intro ω L R h; exact bc110_count_of_globalForest ω L R h

end StatMech.Walls
