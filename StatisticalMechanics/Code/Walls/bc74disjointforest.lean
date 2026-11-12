/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































import Mathlib
import Code.Walls.bc73sublattice
import Code.Walls.bc69count
import Code.Percolation.CanonForestCount

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





theorem bc74_fiber_subset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) :
    bc73_fiber ω L R c ⊆ bc61_coarseTrifFinset ω L R := by
  classical
  rw [bc73_fiber]
  exact Finset.filter_subset _ _



theorem bc74_fiber_card_le_coarseTcount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) :
    (bc73_fiber ω L R c).card ≤ bc61_coarseTcount ω L R := by
  rw [bc61_coarseTcount]
  exact Finset.card_le_card (bc74_fiber_subset ω L R c)














theorem bc74_sublatticeForest_of_fullCount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) :
    bc73_SublatticeForest ω L R := by
  intro c
  exact le_trans (bc74_fiber_card_le_coarseTcount ω L R c) h





theorem bc74_sublatticeForest_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc73_SublatticeForest ω L R :=
  bc74_sublatticeForest_of_fullCount ω L R (bc69_coarseTcount_le_boundary ω L R h)





theorem bc74_sublatticeForest_of_forestNeighbours (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc71_GnForestNeighbours ω L R) :
    bc73_SublatticeForest ω L R :=
  bc74_sublatticeForest_of_fullCount ω L R (bc71_count_of_forestNeighbours ω L R h)












theorem bc74_fiber_mem_gnTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) {y : Site d} (hy : y ∈ bc73_fiber ω L R c) :
    bc67_IsGnTrifurcation ω L y := by
  have hmem : y ∈ bc61_coarseTrifFinset ω L R := bc74_fiber_subset ω L R c hy
  rw [bc61_mem_coarseTrifFinset] at hmem
  exact (bc67_coarseTrif_is_G_n_trifurcation ω L y).mp hmem.2






theorem bc74_fiber_disjointBoxes_deg3 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) {y : Site d} (hy : y ∈ bc73_fiber ω L R c) :
    ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S)
      (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj),
      3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩ :=
  bc73_disjointBoxes_deg3 (bc74_fiber_mem_gnTrif ω L R c hy)





theorem bc74_fiber_leaf_inject {p : Site d → Prop} (S : Set (Subtype p)) :
    Set.InjOn (Subtype.val : Subtype p → Site d) S :=
  bc69_subtypeVal_injOn S



















def bc74_FiberForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) : Prop :=
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (G : SimpleGraph (↑S : Type)) (_ : DecidableRel G.Adj) (ιU : Site d → (↑S : Type)),
    G.IsAcyclic ∧ (∀ v, 1 ≤ G.degree v) ∧
    (∀ y, y ∈ bc73_fiber ω L R c → 3 ≤ G.degree (ιU y)) ∧
    (∀ y, y ∈ bc73_fiber ω L R c → ∀ z, z ∈ bc73_fiber ω L R c → ιU y = ιU z → y = z) ∧
    (∀ v : (↑S : Type), G.degree v = 1 → (v : Site d) ∈ vertexBoundary d R)







theorem bc74_fiber_count_of_fiberForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc74_FiberForest ω L R c) :
    (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
  classical
  obtain ⟨S, hSfin, hSne, G, hGdec, ιU, hacyc, hmin, hdeg3, hιinj, hlammap⟩ := h
  set Tf := bc73_fiber ω L R c with hTf
  set Tw : Finset (↑S : Type) := Tf.image ιU with hTw
  
  have hιinjOn : Set.InjOn ιU Tf := by
    intro y hy z hz hyz
    rw [Finset.mem_coe] at hy hz
    exact hιinj y hy z hz hyz
  have hcardTw : Tw.card = Tf.card := by
    rw [hTw, Finset.card_image_of_injOn hιinjOn]
  
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ G.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    exact hdeg3 y hy
  
  calc Tf.card = Tw.card := hcardTw.symm
    _ ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card :=
        flc2_trifImage_card_le_deg3 G Tw hTwdeg
    _ ≤ (univ.filter (fun v => G.degree v = 1)).card :=
        flc2_forest_internal_le_leaves G hacyc hmin
    _ ≤ boxSV_boundaryCard d R :=
        flc2_leaf_card_le_boundary G R (Subtype.val : (↑S : Type) → Site d) hlammap
          (bc69_subtypeVal_injOn _)






theorem bc74_sublatticeForest_of_fiberForests (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : ∀ c : Fin d → Fin (2 * L + 1), bc74_FiberForest ω L R c) :
    bc73_SublatticeForest ω L R :=
  fun c => bc74_fiber_count_of_fiberForest ω L R c (h c)













theorem bc74_fiber_mem_box (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) {y : Site d} (hy : y ∈ bc73_fiber ω L R c) :
    y ∈ box d R := by
  have hmem : y ∈ bc61_coarseTrifFinset ω L R := bc74_fiber_subset ω L R c hy
  rw [bc61_mem_coarseTrifFinset] at hmem
  exact hmem.1






theorem bc74_fiberForest_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc69_Gn_globalForest ω L R) :
    bc74_FiberForest ω L R c := by
  obtain ⟨S, hSfin, hSne, G, hGdec, ιU, hacyc, hmin, hdeg3, hιinj, hlammap⟩ := h
  refine ⟨S, hSfin, hSne, G, hGdec, ιU, hacyc, hmin, ?_, ?_, hlammap⟩
  · intro y hy
    exact hdeg3 y (bc74_fiber_mem_box ω L R c hy) (bc74_fiber_mem_gnTrif ω L R c hy)
  · intro y hy z hz hyz
    exact hιinj y (bc74_fiber_mem_box ω L R c hy) (bc74_fiber_mem_gnTrif ω L R c hy)
      z (bc74_fiber_mem_box ω L R c hz) (bc74_fiber_mem_gnTrif ω L R c hz) hyz













theorem bc74_fiberForest_of_emptyFiber (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (hempty : bc73_fiber ω L R c = ∅)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) :
    bc74_FiberForest ω L R c := by
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
  have hVall : ∀ v : (↑S : Type), v = a ∨ v = b := by
    intro v
    obtain ⟨x, hx⟩ := v
    rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · left; rfl
    · right; rfl
  have hda : G.degree a = 1 := bc69_single_edge_degree a b hab
  have hdb : G.degree b = 1 := bc69_single_edge_degree_b a b hab
  refine ⟨S, hSfin, ⟨a⟩, G, hGdec, (fun _ => a), bc69_single_edge_acyclic a b hab, ?_, ?_, ?_, ?_⟩
  · intro v; rcases hVall v with rfl | rfl
    · rw [hda]
    · rw [hdb]
  · 
    intro y hy; rw [hempty] at hy; exact absurd hy (Finset.notMem_empty y)
  · 
    intro y hy; rw [hempty] at hy; exact absurd hy (Finset.notMem_empty y)
  · 
    intro v _; rcases hVall v with rfl | rfl
    · exact hz₀
    · exact hz₁





theorem bc74_sublatticeForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hno : bc61_coarseTrifFinset ω L R = ∅) :
    bc73_SublatticeForest ω L R := by
  classical
  refine bc74_sublatticeForest_of_fiberForests ω L R (fun c => ?_)
  have hfib : bc73_fiber ω L R c = ∅ := by rw [bc73_fiber, hno]; simp
  exact bc74_fiberForest_of_emptyFiber ω L R c hfib hz₀ hz₁ hzne














theorem bc74_bk_count_closed
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc73_infiniteClusters_top_null μ hd L hexp hforest hexist






theorem bc74_bk_count_closed_of_globalForest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc74_bk_count_closed μ hd L hexp
    (fun ω R => bc74_sublatticeForest_of_globalForest ω L R (hGlobal ω R)) hexist























theorem bc74_upperLines_sameResidue (L : ℕ) :
    bc73_resVec L (0 : Site 2) = bc73_resVec L (bc57_pt (2 * (L : ℤ) + 1) 0) := by
  funext i
  apply Fin.ext
  simp only [bc73_resVec]
  have hzero0 : (0 : Site 2) 0 = 0 := rfl
  have hzero1 : (0 : Site 2) 1 = 0 := rfl
  fin_cases i
  · 
    change ((0 : Site 2) 0 % (2 * (L : ℤ) + 1)).toNat
      = ((bc57_pt (2 * (L : ℤ) + 1) 0) 0 % (2 * (L : ℤ) + 1)).toNat
    rw [bc57_pt_fst, hzero0, Int.zero_emod, Int.emod_self]
  · 
    change ((0 : Site 2) 1 % (2 * (L : ℤ) + 1)).toNat
      = ((bc57_pt (2 * (L : ℤ) + 1) 0) 1 % (2 * (L : ℤ) + 1)).toNat
    rw [bc57_pt_snd, hzero1]




theorem bc74_upperLines_sublattice_disjoint (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) :=
  bc73_upperLines_sublattice_disjoint L




theorem bc74_upperLines_deg3_sublattice {L : ℕ} (hL : 3 ≤ L) :
    ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (hyS : (0 : Site 2) ∈ S)
      (_ : DecidableRel ((bc72_quotGraph (openSubgraph 2 bc60_upperLines)
              (bc72_collapseBox L (0 : Site 2))).induce S).Adj),
      3 ≤ ((bc72_quotGraph (openSubgraph 2 bc60_upperLines)
            (bc72_collapseBox L (0 : Site 2))).induce S).degree ⟨0, hyS⟩ :=
  bc73_upperLines_deg3_sublattice hL










theorem bc74_upperLines_arms_can_share_boundary (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc64_arms_can_share_boundary L
























theorem bc74_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)),
      bc74_FiberForest ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)) (y : Site d),
      y ∈ bc73_fiber ω L R c →
      ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S)
        (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj),
        3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc71_GnForestNeighbours ω L R → bc73_SublatticeForest ω L R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L R c h; exact bc74_fiber_count_of_fiberForest ω L R c h
  · intro ω L R c y hy; exact bc74_fiber_disjointBoxes_deg3 ω L R c hy
  · intro ω L R h; exact bc74_sublatticeForest_of_forestNeighbours ω L R h

end StatMech.Walls
