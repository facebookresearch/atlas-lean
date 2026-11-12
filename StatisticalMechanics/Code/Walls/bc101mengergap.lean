/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.Walls.bc67supervertex
import Code.Walls.bc64coarseembed
import Code.Walls.bc99connect

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}















theorem bc101_gnTrif_three_incident_arms (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
      ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
       (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
       (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hincs, hinf, hcuts⟩ := bc67_gnTrif_of_coarseTrif ω L y h
  exact ⟨a₁, a₂, a₃, hincs, hinf, hcuts⟩






theorem bc101_arm_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z :=
  bc67_Gn_arm_reaches_boundary ω L R hR y a habox hinf
















theorem bc101_mngg_available_but_free (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      
      (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
      
      (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hincs, _hinf, hcuts⟩ := bc101_gnTrif_three_incident_arms ω L y h
  exact ⟨a₁, a₂, a₃, hincs, hcuts⟩















theorem bc101_residue_is_boundary_injection (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc61_CoarseForestLeafCount ω L R :=
  (bc63_coarseArmEmbedding_iff_forestLeafCount ω L R).mp
    (bc64_coarseArmEmbedding_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj)





theorem bc101_coarseTcount_of_boundaryInjection (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc61_coarseTcount_le_boundary_of_forest ω L R
    (bc101_residue_is_boundary_injection ω L R hz₀ hz₁ hzne hinj)














theorem bc101_named_residue_wrong_scale {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
      ¬ bc56_BoxClusterReachesNbr 2 3 :=
  bc99_notFree_of_coarseTrif hL










theorem bc101_three_arms_upperLines {L : ℕ} (hL : 3 ≤ L) :
    ∃ a₁ a₂ a₃ : Site 2,
      (bc67_GnIncident bc60_upperLines L 0 a₁ ∧ bc67_GnIncident bc60_upperLines L 0 a₂ ∧
        bc67_GnIncident bc60_upperLines L 0 a₃) ∧
      (¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable a₂ a₃) :=
  bc101_mngg_available_but_free bc60_upperLines L 0 (bc61_wholeBox_severs_upperLines hL)

























theorem bc101_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d),
      bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site d,
        (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
        (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
         ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
         ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
        ¬ bc56_BoxClusterReachesNbr 2 3) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R →
      bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L y h; exact bc101_mngg_available_but_free ω L y h
  · intro L hL; exact bc101_named_residue_wrong_scale hL
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hinj
    exact bc101_coarseTcount_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj

end StatMech.Walls
