/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































































import Mathlib
import Code.Walls.bc80gntrifcount
import Code.Walls.bc76buffer
import Code.Walls.bc75spanningtree
import Code.Percolation.ForestLeafCountClose

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


















theorem bc84_peeling_forest_le_boundary {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (R : ℕ) (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (lam : W → Site d)
    (hmap : ∀ v, G.degree v = 1 → lam v ∈ vertexBoundary d R)
    (hinj : Set.InjOn lam (univ.filter (fun v => G.degree v = 1))) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ boxSV_boundaryCard d R :=
  le_trans (flc2_forest_internal_le_leaves G hacyc hmin)
    (flc2_leaf_card_le_boundary G R lam hmap hinj)









open Classical in





theorem bc84_leafBoundaryInj_of_boundaryLeaves (S : Set (Site d)) [Fintype (↑S : Type)]
    (H : SimpleGraph (↑S : Type)) [DecidableRel H.Adj] (R : ℕ)
    (hleafmap : ∀ v : (↑S : Type), H.degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
    (∀ v : (↑S : Type), H.degree v = 1 → (Subtype.val v) ∈ vertexBoundary d R) ∧
      Set.InjOn Subtype.val
        (↑(Finset.univ.filter (fun v => H.degree v = 1)) : Set (↑S : Type)) := by
  refine ⟨hleafmap, ?_⟩
  intro a _ b _ hab
  exact Subtype.ext hab

open Classical in






theorem bc84_fiber_bound_of_assembled (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (H : SimpleGraph (↑S : Type)) [DecidableRel H.Adj]
    (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S)
    (hacyc : H.IsAcyclic) (hmin : ∀ v : (↑S : Type), 1 ≤ H.degree v)
    (hdeg3 : ∀ y (hy : y ∈ bc73_fiber ω L R c), 3 ≤ H.degree ⟨y, hyS y hy⟩)
    (hleafmap : ∀ v : (↑S : Type), H.degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
    (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
  classical
  
  have hfib_le_deg3 : (bc73_fiber ω L R c).card
      ≤ (Finset.univ.filter (fun v : (↑S : Type) => 3 ≤ H.degree v)).card := by
    set ι : Site d → (↑S : Type) := fun y => if hy : y ∈ bc73_fiber ω L R c then ⟨y, hyS y hy⟩
      else Classical.arbitrary (↑S : Type) with hι
    refine Finset.card_le_card_of_injOn ι ?_ ?_
    · intro y hy
      have hy' : y ∈ bc73_fiber ω L R c := hy
      have hιeq : ι y = ⟨y, hyS y hy'⟩ := by simp only [hι, dif_pos hy']
      rw [Finset.mem_coe, Finset.mem_filter, hιeq]
      exact ⟨Finset.mem_univ _, hdeg3 y hy'⟩
    · intro y hy z hz hyz
      have hy' : y ∈ bc73_fiber ω L R c := hy
      have hz' : z ∈ bc73_fiber ω L R c := hz
      have hιy : ι y = ⟨y, hyS y hy'⟩ := by simp only [hι, dif_pos hy']
      have hιz : ι z = ⟨z, hyS z hz'⟩ := by simp only [hι, dif_pos hz']
      rw [hιy, hιz] at hyz
      exact congrArg Subtype.val hyz
  
  obtain ⟨hmap, hinj⟩ := bc84_leafBoundaryInj_of_boundaryLeaves S H R hleafmap
  exact le_trans hfib_le_deg3 (bc84_peeling_forest_le_boundary H R hacyc hmin Subtype.val hmap hinj)












open Classical in




theorem bc84_gnTrifData_components (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
      (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S),
      (bc75_spanForest ω L R c S).IsAcyclic ∧
      (∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) ∧
      (∀ y (hy : y ∈ bc73_fiber ω L R c), 3 ≤ (bc75_spanForest ω L R c S).degree ⟨y, hyS y hy⟩) ∧
      (∀ v : (↑S : Type), (bc75_spanForest ω L R c S).degree v = 1 →
        (v : Site d) ∈ vertexBoundary d R) := by
  classical
  obtain ⟨S, hSfin, hSne, hyS, htriData, hmin, hleaf⟩ := h
  refine ⟨S, hSfin, hSne, hyS, bc75_spanForest_acyclic ω L R c S, hmin, ?_, hleaf⟩
  intro y hy
  obtain ⟨v₁, v₂, v₃, h₁, h₂, h₃, hc₁₂, hc₁₃, hc₂₃⟩ := htriData y hy
  exact bc75_deg3_in_spanForest_of_gnCut ω L R c (hyS y hy) h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃

open Classical in





theorem bc84_fiber_bound_of_gnTrifData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
  classical
  obtain ⟨S, hSfin, hSne, hyS, hacyc, hmin, hdeg3, hleafmap⟩ :=
    bc84_gnTrifData_components ω L R c h
  haveI : Nonempty (↑S : Type) := hSne
  exact bc84_fiber_bound_of_assembled ω L R c S (bc75_spanForest ω L R c S)
    hyS hacyc hmin hdeg3 hleafmap















theorem bc84_leaf_boundary_is_perConfig {W : Type*} [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (R : ℕ) (lam : W → Site d)
    (hmap : ∀ v, G.degree v = 1 → lam v ∈ vertexBoundary d R)
    (hinj : Set.InjOn lam (univ.filter (fun v => G.degree v = 1))) :
    (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d R :=
  flc2_leaf_card_le_boundary G R lam hmap hinj























theorem bc84_upperLines_obstruction_is_cut {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
  bc76_buffer_insufficient hL






theorem bc84_upperLines_coarseTrif_and_top {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
      numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  ⟨bc61_wholeBox_severs_upperLines hL, bc60_numInfiniteClusters_top⟩





































theorem bc84_status :
    
    (∀ (W : Type) (_ : Fintype W) (_ : Nonempty W) (G : SimpleGraph W) (_ : DecidableRel G.Adj)
        (R : ℕ) (lam : W → Site 2),
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (∀ v, G.degree v = 1 → lam v ∈ vertexBoundary 2 R) →
      Set.InjOn lam (univ.filter (fun v => G.degree v = 1)) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (W : Type) (_ : Fintype W) (G : SimpleGraph W) (_ : DecidableRel G.Adj) (R : ℕ)
        (lam : W → Site 2),
      (∀ v, G.degree v = 1 → lam v ∈ vertexBoundary 2 R) →
      Set.InjOn lam (univ.filter (fun v => G.degree v = 1)) →
      (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1)),
      bc75_FiberGnTrifData ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
        ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
        ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W _ _ G _ R lam hacyc hmin hmap hinj
    exact bc84_peeling_forest_le_boundary G R hacyc hmin lam hmap hinj
  · intro W _ G _ R lam hmap hinj
    exact bc84_leaf_boundary_is_perConfig G R lam hmap hinj
  · intro ω L R c h; exact bc84_fiber_bound_of_gnTrifData ω L R c h
  · intro L hL; exact (bc84_upperLines_obstruction_is_cut hL).2.2

end StatMech.Walls
