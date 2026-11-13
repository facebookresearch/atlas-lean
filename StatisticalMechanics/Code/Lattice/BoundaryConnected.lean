/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.PlanarTopology
import Code.Lattice.ContourAnchor
import Code.Lattice.EnclosingLength
import Code.Lattice.LeftFace
import Code.Lattice.UniqueInfiniteComponent
import Code.Percolation.PcUpperUncond

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)







variable {d : ℕ}




theorem exterior_mem_infiniteComponent (hd : 2 ≤ d) (F : Set (Site d)) (R : ℕ)
    (hR : F ⊆ box d R) {x : Site d} (hx : x ∈ exterior d R) :
    (((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨x, exterior_subset_compl F R hR hx⟩).supp.Infinite := by
  classical
  set G := (hypercubicLattice d).induce Fᶜ with hG
  have hsub : exterior d R ⊆ Fᶜ := exterior_subset_compl F R hR
  set C := G.connectedComponentMk ⟨x, hsub hx⟩ with hC
  have : Infinite ↥(exterior d R) := (exterior_infinite R hd).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior d R) => (⟨(w : Site d), hsub w.2⟩ : ↥Fᶜ)) ?_ ?_
  · intro a b hab
    exact Subtype.ext (by simpa using congrArg Subtype.val hab)
  · intro w
    rw [ConnectedComponent.mem_supp_iff, hC]
    exact ConnectedComponent.sound
      (exterior_reachable_compl F R hd hsub (w : Site d) x w.2 hx)



theorem exterior_reachable_in_compl (hd : 2 ≤ d) (F : Set (Site d)) (R : ℕ)
    (hR : F ⊆ box d R) {x y : Site d} (hx : x ∈ exterior d R) (hy : y ∈ exterior d R) :
    ((hypercubicLattice d).induce Fᶜ).Reachable
      ⟨x, exterior_subset_compl F R hR hx⟩ ⟨y, exterior_subset_compl F R hR hy⟩ :=
  exterior_reachable_compl F R hd (exterior_subset_compl F R hR) x y hx hy



theorem exterior_connectedComponent_eq (hd : 2 ≤ d) (F : Set (Site d)) (R : ℕ)
    (hR : F ⊆ box d R) {x y : Site d} (hx : x ∈ exterior d R) (hy : y ∈ exterior d R) :
    ((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨x, exterior_subset_compl F R hR hx⟩
      = ((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨y, exterior_subset_compl F R hR hy⟩ :=
  ConnectedComponent.sound (exterior_reachable_in_compl hd F R hR hx hy)



variable {ω : ConfigSpace (Sym2 (Site 2))}





theorem clusterComplement_unique_infiniteComponent (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃! C : ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).ConnectedComponent,
      C.supp.Infinite :=
  unique_infinite_component (by norm_num) (cluster 2 ω (origin 2)) hfin


theorem exists_clusterBox (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ R : ℕ, cluster 2 ω (origin 2) ⊆ box 2 R :=
  finite_subset_box _ hfin


theorem axisFarRight_mem_exterior (R : ℕ) : (![(R : ℤ) + 1, 0] : Site 2) ∈ exterior 2 R := by
  refine ⟨0, ?_⟩
  show R < (((R : ℤ) + 1)).natAbs
  rw [show ((R : ℤ) + 1).natAbs = R + 1 by rw [Int.natAbs_eq_iff]; left; push_cast; ring]
  omega


theorem axisFarLeft_mem_exterior (R : ℕ) : (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := by
  refine ⟨0, ?_⟩
  show R < ((-((R : ℤ) + 1))).natAbs
  rw [show (-((R : ℤ) + 1)).natAbs = R + 1 by rw [Int.natAbs_eq_iff]; right; push_cast; ring]
  omega






theorem axisFar_sameComponent (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).connectedComponentMk
        ⟨![(R : ℤ) + 1, 0],
          exterior_subset_compl _ R hR (axisFarRight_mem_exterior R)⟩
      = ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).connectedComponentMk
        ⟨![-((R : ℤ) + 1), 0],
          exterior_subset_compl _ R hR (axisFarLeft_mem_exterior R)⟩ :=
  exterior_connectedComponent_eq (by norm_num) (cluster 2 ω (origin 2)) R hR
    (axisFarRight_mem_exterior R) (axisFarLeft_mem_exterior R)






theorem axisFar_reachable_in_clusterComplement (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨![(R : ℤ) + 1, 0], exterior_subset_compl _ R hR (axisFarRight_mem_exterior R)⟩
      ⟨![-((R : ℤ) + 1), 0], exterior_subset_compl _ R hR (axisFarLeft_mem_exterior R)⟩ :=
  exterior_reachable_in_compl (by norm_num) (cluster 2 ω (origin 2)) R hR
    (axisFarRight_mem_exterior R) (axisFarLeft_mem_exterior R)




theorem axisFarRight_infiniteComponent (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    (((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).connectedComponentMk
        ⟨![(R : ℤ) + 1, 0],
          exterior_subset_compl _ R hR (axisFarRight_mem_exterior R)⟩).supp.Infinite :=
  exterior_mem_infiniteComponent (by norm_num) (cluster 2 ω (origin 2)) R hR
    (axisFarRight_mem_exterior R)




























def EnclosingContourLinksExits (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ∃ c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
      (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin),
    c.IsCycle ∧ leftExitFaceUp (ω := ω) hfin ∈ c.support





theorem cycleHasLeftFace_of_enclosingContourLinksExits (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : EnclosingContourLinksExits ω hfin) : CycleHasLeftFace ω hfin := by
  obtain ⟨c, hcyc, hmem⟩ := h
  exact ⟨c, hcyc, leftExitFaceUp (ω := ω) hfin, hmem,
    leftExitFaceUp_coord0_nonpos (ω := ω) hfin⟩




theorem anchoredCycleExists_of_enclosingContourLinksExits
    (hfin : (cluster 2 ω (origin 2)).Finite) (h : EnclosingContourLinksExits ω hfin) :
    AnchoredCycleExists ω hfin :=
  anchoredCycleExists_of_leftFace (ω := ω) hfin
    (cycleHasLeftFace_of_enclosingContourLinksExits (ω := ω) hfin h)




theorem pcAnchoredEnclosure_of_enclosingContourLinksExits
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure :=
  pcAnchoredEnclosure_of_cycleHasLeftFace
    (fun ω hfin => cycleHasLeftFace_of_enclosingContourLinksExits (ω := ω) hfin (h ω hfin))






theorem pc_lt_one_via_boundary
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  StatMech.Percolation.pc_lt_one_of_enclosure
    (pcAnchoredEnclosure_of_enclosingContourLinksExits h)





































end Lattice

end StatMech
