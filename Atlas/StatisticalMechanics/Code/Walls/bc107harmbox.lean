/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Walls.bc101mengergap
import Code.Walls.bc90boxopenforest
import Code.Walls.bc70globalforest
import Code.Walls.bc62coarseclose

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












theorem bc107_harmbox_free_interior (ω : ConfigSpace (Sym2 (Site d))) {n : ℕ} (hn : 1 ≤ n)
    {x : Site d} (hxint : x ∈ box d (n - 1))
    {a : Site d} (hadj : (openSubgraph d ω).Adj x a) : a ∈ box d n :=
  bc90_harmbox_free_of_interior ω hn hxint hadj





theorem bc107_harmbox_obstruction_is_boundary (ω : ConfigSpace (Sym2 (Site d))) {n : ℕ} (hn : 1 ≤ n)
    {x a : Site d} (hx : x ∈ box d n) (hadj : (openSubgraph d ω).Adj x a) (ha : a ∉ box d n) :
    x ∉ box d (n - 1) :=
  cfc_neighbour_outside_box_imp_boundary hn hx hadj.1 ha
















theorem bc107_harmbox_discharged_at_coarse_scale (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hR : 1 ≤ R) (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z :=
  bc101_arm_reaches_boundary ω L R hR y a habox hinf







theorem bc107_three_arms_reach_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y : Site d) (h : bc61_IsCoarseTrifurcation ω L y)
    {a₁ a₂ a₃ : Site d} (hbox : a₁ ∈ box d R ∧ a₂ ∈ box d R ∧ a₃ ∈ box d R)
    (harmsub : (cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
      (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
      (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) :
    (∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a₁ z) ∧
    (∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a₂ z) ∧
    (∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a₃ z) :=
  ⟨bc101_arm_reaches_boundary ω L R hR y a₁ hbox.1 harmsub.1,
   bc101_arm_reaches_boundary ω L R hR y a₂ hbox.2.1 harmsub.2.1,
   bc101_arm_reaches_boundary ω L R hR y a₃ hbox.2.2 harmsub.2.2⟩
















theorem bc107_coarseRoute_armReach_free (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z :=
  bc101_arm_reaches_boundary ω L R hR y a habox hinf






theorem bc107_coarseRoute_precursor_genuine
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (hpos : 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} :=
  bc62_coarseTrif_pos_of_precursor_pos μ hfe L a₁ a₂ a₃ b₁ b₂ b₃ hpos















theorem bc107_bk_residue_after_harmbox_discharge
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc69_infiniteClusters_top_null_of_globalForest μ hd hinv hfe L hGlobal hcoarseRoute










theorem bc107_armReach_upperLines {L R : ℕ} (hR : 1 ≤ R) (y a : Site 2) (habox : a ∈ box 2 R)
    (hinf : (cluster 2 (removeSites (bc61_boxAround 2 L y) bc60_upperLines) a).Infinite) :
    ∃ z ∈ vertexBoundary 2 R, (bc67_contractedLattice bc60_upperLines L y).Reachable a z :=
  bc101_arm_reaches_boundary bc60_upperLines L R hR y a habox hinf







theorem bc107_precursor_witness (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d) (hω : ω ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) :
    bc61_IsCoarseTrifurcation
      (forceOpenFinset {s(b₁, a₁), s(b₂, a₂), s(b₃, a₃)} ω) L 0 :=
  bc62_coarseTrif_of_precursor_mem ω L a₁ a₂ a₃ b₁ b₂ b₃ hω

































theorem bc107_status (hd : 1 ≤ d) :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → ∀ {x : Site d}, x ∈ box d (n - 1) →
      ∀ {a : Site d}, (openSubgraph d ω).Adj x a → a ∈ box d n) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ],
      HasFiniteEnergyMerge μ → ∀ (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d),
      0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) →
      0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0}) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
      (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
      (hfe : HasFiniteEnergyMerge μ) (L : ℕ),
      (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R) →
      (0 < μ {ω | numInfiniteClusters d ω = ⊤} →
        ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
          0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L R hR y a habox hinf
    exact bc107_harmbox_discharged_at_coarse_scale ω L R hR y a habox hinf
  · intro ω n hn x hxint a hadj
    exact bc107_harmbox_free_interior ω hn hxint hadj
  · intro ω L R hR y a habox hinf
    exact bc107_coarseRoute_armReach_free ω L R hR y a habox hinf
  · intro μ _ hfe L a₁ a₂ a₃ b₁ b₂ b₃ hpos
    exact bc107_coarseRoute_precursor_genuine μ hfe L a₁ a₂ a₃ b₁ b₂ b₃ hpos
  · intro μ _ hinv hfe L hGlobal hcoarseRoute
    exact bc107_bk_residue_after_harmbox_discharge μ hd hinv hfe L hGlobal hcoarseRoute

end StatMech.Walls
