/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































































import Mathlib
import Code.Walls.bc106separated
import Code.Walls.bc102armleafboundary
import Code.Walls.bc103contractdeg

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









theorem bc108_fiber_subset_coarseTrifFinset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) :
    bc73_fiber ω L R c ⊆ bc61_coarseTrifFinset ω L R := by
  unfold bc73_fiber
  exact Finset.filter_subset _ _




theorem bc108_fiber_card_le_coarseTcount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) :
    (bc73_fiber ω L R c).card ≤ bc61_coarseTcount ω L R := by
  rw [bc61_coarseTcount]
  exact Finset.card_le_card (bc108_fiber_subset_coarseTrifFinset ω L R c)














theorem bc108_sublatticeForest_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) : bc73_SublatticeForest ω L R := by
  intro c
  calc (bc73_fiber ω L R c).card
      ≤ bc61_coarseTcount ω L R := bc108_fiber_card_le_coarseTcount ω L R c
    _ ≤ boxSV_boundaryCard d R := bc69_count_via_leafBound ω L R h



theorem bc108_sublatticeForest_of_contractedGraph (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc103_ContractedTrifGraph ω L R) : bc73_SublatticeForest ω L R :=
  bc108_sublatticeForest_of_globalForest ω L R (bc103_globalForest_of_contractedGraph ω L R h)











theorem bc108_separatedCount_le_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc106_separated_count_le_boundary_of_forest ω L R (bc108_sublatticeForest_of_globalForest ω L R h)





theorem bc108_full_covering_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R :=
  bc73_covering ω L R (bc108_sublatticeForest_of_globalForest ω L R h)














theorem bc108_hub_three_distinct_forestNeighbours {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel (osf_spanForest G).Adj] {u v₁ v₂ v₃ : V}
    (hadj₁ : G.Adj u v₁) (hadj₂ : G.Adj u v₂) (hadj₃ : G.Adj u v₃)
    (hcut₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
    (hcut₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
    (hcut₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) :
    3 ≤ (osf_spanForest G).degree u :=
  bc103_deg3_spanForest_of_noBypass G hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃




theorem bc108_hub_arms_distinct {V : Type*} {G : SimpleGraph V} {u v₁ v₂ v₃ : V}
    (hcut₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
    (hcut₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
    (hcut₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) :
    v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ :=
  bc103_arms_distinct_of_deleteVert_cut hcut₁₂ hcut₁₃ hcut₂₃


















theorem bc108_crosshub_leaves_can_share (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc102_bc64_crossSV_refuted L









theorem bc108_boundary_injection_refuted (L : ℕ) :
    
    (Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0))) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc108_crosshub_leaves_can_share L

















theorem bc108_bk_count_reduces_to_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    (bc69_Gn_globalForest ω L R → bc73_SublatticeForest ω L R) ∧
    (bc69_Gn_globalForest ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    (bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) :=
  ⟨bc108_sublatticeForest_of_globalForest ω L R,
   bc108_separatedCount_le_of_globalForest ω L R,
   bc69_count_via_leafBound ω L R⟩
















theorem bc108_infiniteClusters_top_null_of_globalForest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc73_infiniteClusters_top_null μ hd L hexp
    (fun ω R => bc108_sublatticeForest_of_globalForest ω L R (hGlobal ω R)) hexist












theorem bc108_sublatticeForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc73_SublatticeForest ω L R :=
  bc108_sublatticeForest_of_globalForest ω L R
    (bc102_connectedForest_of_noTrif ω L R hz₀ hz₁ hzne hno)







































theorem bc108_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc73_SublatticeForest ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)),
      (bc73_fiber ω L R c).card ≤ bc61_coarseTcount ω L R) ∧
    
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧
    
    (∀ {V : Type} {G : SimpleGraph V} (u v₁ v₂ v₃ : V),
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ →
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L R h; exact bc108_sublatticeForest_of_globalForest ω L R h
  · intro ω L R c; exact bc108_fiber_card_le_coarseTcount ω L R c
  · intro L; exact bc108_crosshub_leaves_can_share L
  · intro V G u v₁ v₂ v₃ hc₁₂ hc₁₃ hc₂₃; exact bc108_hub_arms_distinct hc₁₂ hc₁₃ hc₂₃
  · intro ω L R h; exact bc108_separatedCount_le_of_globalForest ω L R h

end StatMech.Walls

