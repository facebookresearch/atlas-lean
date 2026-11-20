/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































































import Mathlib
import Code.Walls.bc85bootstrap
import Code.Walls.bc84leafboundary
import Code.Walls.bc81gncutae
import Code.Walls.bc80gntrifcount
import Code.Walls.bc64coarseembed

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

















theorem bc86_sublatticeForest_of_gnData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hgn : ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
    bc73_SublatticeForest ω L R :=
  fun c => bc84_fiber_bound_of_gnTrifData ω L R c (hgn c)






theorem bc86_count_on_empty_coarseTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hno : bc61_coarseTrifFinset ω L R = ∅) :
    bc73_SublatticeForest ω L R :=
  bc73_sublatticeForest_of_noTrif ω L R hno

























theorem bc86_coarseTrif_is_branchpoint (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
      (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
      (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite ∧
      ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
      ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
      ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃ := by
  obtain ⟨a₁, a₂, a₃, _, _, _, ⟨hi₁, hi₂, hi₃⟩, hc₁₂, hc₁₃, hc₂₃⟩ := h
  exact ⟨a₁, a₂, a₃, hi₁, hi₂, hi₃, hc₁₂, hc₁₃, hc₂₃⟩









theorem bc86_singleBox_cut_free_of_le_one (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
      ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
      ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃ := by
  obtain ⟨a₁, a₂, a₃, _, hcut⟩ := bc81_singleBox_no_gap ω L y h
  exact ⟨a₁, a₂, a₃, hcut⟩








theorem bc86_arms_connected_and_cut_disconnected_of_le_one (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    {y : Site d} (hN : numInfiniteClusters d ω ≤ 1) (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (Connected d ω a₁ a₂ ∧ Connected d ω a₁ a₃ ∧ Connected d ω a₂ a₃) ∧
      (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hc₁₂, hc₁₃, hc₂₃, hcut⟩ :=
    bc81_coarseTrif_arms_connected_of_le_one ω L hN h
  exact ⟨a₁, a₂, a₃, ⟨hc₁₂, hc₁₃, hc₂₃⟩, hcut⟩




















theorem bc86_fiber_arms_can_coincide (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y y' : Site d}
    (hN : numInfiniteClusters d ω ≤ 1)
    (h : bc61_IsCoarseTrifurcation ω L y) (h' : bc61_IsCoarseTrifurcation ω L y') :
    ∃ a a' : Site d,
      (cluster d ω a).Infinite ∧ (cluster d ω a').Infinite ∧ Connected d ω a a' := by
  obtain ⟨a₁, _, _, hinf₁, _, _, _⟩ := bc81_cut_cluster_infinite_of_coarse ω L h
  obtain ⟨a₁', _, _, hinf₁', _, _, _⟩ := bc81_cut_cluster_infinite_of_coarse ω L h'
  exact ⟨a₁, a₁', hinf₁, hinf₁',
    bc81_infinite_clusters_coincide_of_le_one ω hN hinf₁ hinf₁'⟩








theorem bc86_count_holds_of_le_one_and_gnData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hN : numInfiniteClusters d ω ≤ 1)
    (hgn : ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
    bc73_SublatticeForest ω L R :=
  bc86_sublatticeForest_of_gnData ω L R hgn






theorem bc86_upperLines_N_top :
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc85_upperLines_N_top















theorem bc86_ae_count_of_ae_gnData (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ)
    (hgn_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
    ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R := by
  intro R
  filter_upwards [hgn_ae R] with ω hω
  exact bc86_sublatticeForest_of_gnData ω L R hω







theorem bc86_bk_from_ae_gnData (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hgn_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc85_dc_bootstrap μ hd L hinv (bc86_ae_count_of_ae_gnData μ L hgn_ae) hexist






theorem bc86_finiteN_ae (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hgn_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω < ⊤} = 1 :=
  (bc85_finiteN_iff_top_null μ).mpr (bc86_bk_from_ae_gnData μ hd L hinv hgn_ae hexist)




















theorem bc86_upperLines_emptyFiber_count {L R : ℕ} (hR : 1 ≤ R)
    (c : Fin 2 → Fin (2 * L + 1)) (hempty : bc73_fiber bc60_upperLines L R c = ∅) :
    (bc73_fiber bc60_upperLines L R c).card ≤ boxSV_boundaryCard 2 R :=
  bc84_fiber_bound_of_gnTrifData bc60_upperLines L R c
    (bc75_upperLines_emptyFiber_gnTrifData hR c hempty)








theorem bc86_upperLines_gnCut_needs_buffer (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc75_upperLines_gnCut_needs_buffer L




























theorem bc86_cardinal_verdict (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ),
      (∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) →
      bc73_SublatticeForest ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (y : Site d), bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site d,
        ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧
    
    ((∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) →
      bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨fun ω R hgn => bc86_sublatticeForest_of_gnData ω L R hgn, ?_, ?_⟩
  · intro ω y h; exact bc86_singleBox_cut_free_of_le_one ω L h
  · intro hgn_ae hexist; exact bc86_bk_from_ae_gnData μ hd L hinv hgn_ae hexist







































theorem bc86_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      (∀ c : Fin 2 → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) →
      bc73_SublatticeForest ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site 2,
        ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y y' : Site 2), numInfiniteClusters 2 ω ≤ 1 →
      bc61_IsCoarseTrifurcation ω L y → bc61_IsCoarseTrifurcation ω L y' →
      ∃ a a' : Site 2,
        (cluster 2 ω a).Infinite ∧ (cluster 2 ω a').Infinite ∧ Connected 2 ω a a') ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin 2 → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L R hgn; exact bc86_sublatticeForest_of_gnData ω L R hgn
  · intro ω L y h; exact bc86_singleBox_cut_free_of_le_one ω L h
  · intro ω L y y' hN h h'; exact bc86_fiber_arms_can_coincide ω L hN h h'
  · intro μ _ L hinv hgn_ae hexist; exact bc86_bk_from_ae_gnData μ (by norm_num) L hinv hgn_ae hexist
  · exact bc86_upperLines_N_top

end StatMech.Walls
