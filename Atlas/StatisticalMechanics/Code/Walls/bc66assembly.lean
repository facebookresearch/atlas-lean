/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Walls.bc65connected
import Code.Percolation.CanonForestCount

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}














theorem bc66_coarseTrif_arms_reach (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z :=
  bc63_coarseArm_reaches_boundary ω L R hR y a habox hinf














theorem bc66_leaf_boundary_injection {W : Type*} [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (R : ℕ) (lam : W → Site d)
    (hmap : ∀ v, G.degree v = 1 → lam v ∈ vertexBoundary d R)
    (hinj : Set.InjOn lam (univ.filter (fun v => G.degree v = 1))) :
    (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d R :=
  flc2_leaf_card_le_boundary G R lam hmap hinj





theorem bc66_connected_leaf_count {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  flc2_forest_internal_le_leaves G hacyc hmin















theorem bc66_connectedForest_of_forestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (ιT : Site d → W) (lamL : W → Site d)
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → 3 ≤ G.degree (ιT y))
    (hιinj : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc61_IsCoarseTrifurcation ω L z → ιT y = ιT z → y = z)
    (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
    (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
    bc65_ConnectedCoarseForest ω L R :=
  bc65_connectedForest_of_forestData ω L R W G ιT lamL hacyc hmin hdeg3 hιinj hlammap hlaminj
















theorem bc66_coarseForest_of_boundaryInjection (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc65_ConnectedCoarseForest ω L R :=
  bc65_connectedForest_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj




theorem bc66_coarseTcount_le_boundary_of_connectedForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc65_ConnectedCoarseForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc65_coarseTcount_le_boundary_of_connectedForest ω L R h



















theorem bc66_wholeBox_severs_adversary {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) :=
  bc61_wholeBox_severs_upperLines hL





theorem bc66_adversary_arm_reaches_boundary {L R : ℕ} (hR : 1 ≤ R) {h : ℤ} (hh : 1 ≤ h)
    (hbox : bc57_pt ((L : ℤ) + 1) h ∈ box 2 R) :
    ∃ z ∈ vertexBoundary 2 R,
      Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
        (bc57_pt ((L : ℤ) + 1) h) z :=
  bc66_coarseTrif_arms_reach bc60_upperLines L R hR 0 (bc57_pt ((L : ℤ) + 1) h) hbox
    (bc61_upperLines_rightArm_infinite hh)









theorem bc66_shared_boundary_survives (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc64_arms_can_share_boundary L














theorem bc66_connectedForest_caterpillar2 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {y₀ y₁ : Site d} (hy₀box : y₀ ∈ box d R) (hy₁box : y₁ ∈ box d R) (hyne : y₀ ≠ y₁)
    (hy₀tri : bc61_IsCoarseTrifurcation ω L y₀) (hy₁tri : bc61_IsCoarseTrifurcation ω L y₁)
    (hpair : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → y = y₀ ∨ y = y₁)
    (lamL : Fin 6 → Site d)
    (hlammap : ∀ v, bc65_cat2G.degree v = 1 → lamL v ∈ vertexBoundary d R)
    (hlaminj : Set.InjOn lamL (univ.filter (fun v => bc65_cat2G.degree v = 1))) :
    bc65_ConnectedCoarseForest ω L R :=
  bc65_connectedForest_caterpillar2 ω L R hy₀box hy₁box hyne hy₀tri hy₁tri hpair lamL hlammap hlaminj














theorem bc66_infiniteClusters_top_null_of_connectedForest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hconn : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc65_ConnectedCoarseForest ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc65_infiniteClusters_top_null_of_connectedForest_route μ hd hinv hfe L hconn hcoarseRoute






theorem bc66_infiniteClusters_top_null_of_boundaryInjection
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hbdvertices : ∀ R : ℕ, ∃ z₀ z₁ : Site d,
      z₀ ∈ vertexBoundary d R ∧ z₁ ∈ vertexBoundary d R ∧ z₀ ≠ z₁)
    (hbinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc64_CoarseBoundaryInjection ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  refine bc66_infiniteClusters_top_null_of_connectedForest μ hd hinv hfe L (fun ω R => ?_)
    hcoarseRoute
  obtain ⟨z₀, z₁, hz₀, hz₁, hzne⟩ := hbdvertices R
  exact bc66_coarseForest_of_boundaryInjection ω L R hz₀ hz₁ hzne (hbinj ω R)

























theorem bc66_coarse_armReaching_unconditional (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hR : 1 ≤ R) (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z :=
  bc66_coarseTrif_arms_reach ω L R hR y a habox hinf







































theorem bc66_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z) ∧
    
    (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) ∧
    
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R → bc65_ConnectedCoarseForest ω L R) ∧
    
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L R hR y a habox hinf
    exact bc66_coarse_armReaching_unconditional ω L R hR y a habox hinf
  · intro L hL
    exact bc66_wholeBox_severs_adversary hL
  · intro V _ _ G _ hacyc hmin
    exact bc66_connected_leaf_count G hacyc hmin
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hinj
    exact bc66_coarseForest_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj
  · intro L
    exact bc66_shared_boundary_survives L

end StatMech.Walls
