/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareHoleFill
import Code.Universality.FrameChangeIso
import Code.Lattice.EulerFaces

open Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.Universality

noncomputable section


def squareDualClusterCoverage
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat) : Set (Site 2) :=
  ⋃ x ∈ box 2 n, cluster 2 (fci_faceDualConfig omega) x

theorem box_subset_squareDualClusterCoverage
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat) :
    box 2 n ⊆ squareDualClusterCoverage omega n := by
  intro x hx
  rw [squareDualClusterCoverage, Set.mem_iUnion]
  refine ⟨x, ?_⟩
  rw [Set.mem_iUnion]
  exact ⟨hx, self_mem_cluster _ _⟩



theorem squareDualClusterCoverage_finite
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Finite) :
    (squareDualClusterCoverage omega n).Finite := by
  unfold squareDualClusterCoverage
  exact (box_finite 2 n).biUnion (fun x _ => hfinite x)


theorem squareDualClusterCoverage_closed
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    {x y : Site 2} (hx : x ∈ squareDualClusterCoverage omega n)
    (hxy : (fci_faceOpenDual omega).Adj x y) :
    y ∈ squareDualClusterCoverage omega n := by
  simp only [squareDualClusterCoverage, Set.mem_iUnion] at hx ⊢
  obtain ⟨a, haBox, hax⟩ := hx
  refine ⟨a, haBox, ?_⟩
  change (openSubgraph 2 (fci_faceDualConfig omega)).Reachable a y
  have hxy' : (openSubgraph 2 (fci_faceDualConfig omega)).Adj x y := by
    rw [← fci_faceOpenDual_eq_openSubgraph]
    exact hxy
  exact hax.trans hxy'.reachable

private theorem graphReachable_in_barrier
    (G : SimpleGraph (Site 2)) (S : Set (Site 2))
    (hG : G ≤ hypercubicLattice 2)
    (hclosed : ∀ {x y}, x ∈ S → G.Adj x y → y ∈ S)
    {x y : Site 2} (hx : x ∈ S) (hxy : G.Reachable x y) :
    (latticeMinusBarrier S).Reachable x y := by
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih =>
      have hb : b ∈ S := hclosed hx hab
      exact (latticeMinusBarrier_adj_of_both_mem S (hG hab) hx hb).reachable.trans
        (ih hb)

private theorem latticeWalk_reachable_barrier_of_support_subset
    (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hw : ∀ z ∈ w.support, z ∈ S) :
    (latticeMinusBarrier S).Reachable x y := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih =>
      have ha : a ∈ S := hw a (by simp)
      have hb : b ∈ S := hw b (by simp)
      exact (latticeMinusBarrier_adj_of_both_mem S hab ha hb).reachable.trans
        (ih (fun z hz => hw z (by simp [hz])))

private theorem barrier_reachable_to_induce
    (S : Set (Site 2)) {x y : Site 2} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : (latticeMinusBarrier S).Reachable x y) :
    ((hypercubicLattice 2).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨w⟩ := hxy
  let wl : (hypercubicLattice 2).Walk x y :=
    w.map (Hom.ofLE (latticeMinusBarrier_le S))
  have hw : ∀ z ∈ wl.support, z ∈ S := by
    intro z hz
    change z ∈ (w.map (Hom.ofLE (latticeMinusBarrier_le S))).support at hz
    rw [Walk.support_map] at hz
    have hz' : z ∈ w.support := by simpa using hz
    exact (latticeMinusBarrier_sameSide S (w.takeUntil z hz')).mp hx
  exact walk_induce_reachable _ S wl hw hx hy




theorem squareDualClusterCoverage_inside_connected
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat) :
    ∀ a b : Site 2,
      a ∈ squareDualClusterCoverage omega n →
      b ∈ squareDualClusterCoverage omega n →
      (latticeMinusBarrier (squareDualClusterCoverage omega n)).Reachable a b := by
  intro a b ha hb
  simp only [squareDualClusterCoverage, Set.mem_iUnion] at ha hb
  obtain ⟨x, hxBox, hxa⟩ := ha
  obtain ⟨y, hyBox, hyb⟩ := hb
  let dualG := openSubgraph 2 (fci_faceDualConfig omega)
  have hdualG : dualG ≤ hypercubicLattice 2 := fun _ _ h => h.1
  have hclosed : ∀ {u v},
      u ∈ squareDualClusterCoverage omega n → dualG.Adj u v →
        v ∈ squareDualClusterCoverage omega n := by
    intro u v hu huv
    apply squareDualClusterCoverage_closed omega n hu
    rw [fci_faceOpenDual_eq_openSubgraph]
    exact huv
  have hax : (latticeMinusBarrier (squareDualClusterCoverage omega n)).Reachable a x := by
    apply graphReachable_in_barrier dualG _ hdualG hclosed
      (show a ∈ squareDualClusterCoverage omega n from by
        rw [squareDualClusterCoverage, Set.mem_iUnion]
        exact ⟨x, by rw [Set.mem_iUnion]; exact ⟨hxBox, hxa⟩⟩)
    exact hxa.symm
  have hby : (latticeMinusBarrier (squareDualClusterCoverage omega n)).Reachable b y := by
    apply graphReachable_in_barrier dualG _ hdualG hclosed
      (show b ∈ squareDualClusterCoverage omega n from by
        rw [squareDualClusterCoverage, Set.mem_iUnion]
        exact ⟨y, by rw [Set.mem_iUnion]; exact ⟨hyBox, hyb⟩⟩)
    exact hyb.symm
  obtain ⟨w⟩ := (boxInduce_connected n).preconnected
    (⟨x, hxBox⟩ : (box 2 n)) (⟨y, hyBox⟩ : (box 2 n))
  let incl : boxInduce n →g hypercubicLattice 2 :=
    { toFun := Subtype.val
      map_rel' := fun {a b} h => h }
  let wl : (hypercubicLattice 2).Walk x y :=
    w.map incl
  have hwl : ∀ z ∈ wl.support,
      z ∈ squareDualClusterCoverage omega n := by
    intro z hz
    change z ∈ (w.map incl).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    simpa [incl] using box_subset_squareDualClusterCoverage omega n u.2
  have hxy : (latticeMinusBarrier (squareDualClusterCoverage omega n)).Reachable x y :=
    latticeWalk_reachable_barrier_of_support_subset _ wl hwl
  exact hax.trans (hxy.trans hby.symm)



theorem squareHoleFill_closed_of_faceDual_closed
    (omega : ConfigSpace (Sym2 (Site 2)))
    (S : Set (Site 2)) (hS : S.Finite)
    (hclosed : ∀ {x y}, x ∈ S → (fci_faceOpenDual omega).Adj x y → y ∈ S)
    {x y : Site 2} (hx : x ∈ squareHoleFill S hS)
    (hxy : (fci_faceOpenDual omega).Adj x y) :
    y ∈ squareHoleFill S hS := by
  by_cases hxS : x ∈ S
  · exact subset_squareHoleFill S hS (hclosed hxS hxy)
  by_cases hyS : y ∈ S
  · have hxS' := hclosed hyS hxy.symm
    exact (hxS hxS').elim
  intro hyOut
  have hyReach : (latticeMinusBarrier S).Reachable
      (beacon 2 (squareHoleFillRadius S hS)) y := hyOut
  have hbar : (latticeMinusBarrier S).Adj y x :=
    latticeMinusBarrier_adj_of_both_not_mem S hxy.1.symm hyS hxS
  exact hx (hyReach.trans hbar.reachable)



theorem squareDualClusterCoverage_fill_connected
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Finite) :
    let S := squareDualClusterCoverage omega n
    let hS := squareDualClusterCoverage_finite omega n hfinite
    ∀ a b : squareHoleFill S hS,
      ((hypercubicLattice 2).induce (squareHoleFill S hS)).Reachable a b := by
  dsimp only
  let S := squareDualClusterCoverage omega n
  let hS : S.Finite := squareDualClusterCoverage_finite omega n hfinite
  let K := squareHoleFill S hS
  have hzeroS : origin 2 ∈ S :=
    box_subset_squareDualClusterCoverage omega n (by simp [box, origin])
  have hSconn : ∀ a b : S,
      ((hypercubicLattice 2).induce S).Reachable a b := by
    intro a b
    exact barrier_reachable_to_induce S a.2 b.2
      (squareDualClusterCoverage_inside_connected omega n a b a.2 b.2)
  intro a b
  exact barrier_reachable_to_induce K a.2 b.2
    (squareHoleFill_inside_connected S hS ⟨origin 2, hzeroS⟩ hSconn
      a b a.2 b.2)



theorem squareDualClusterCoverage_faceBoundaryConnected
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Finite) :
    let S := squareDualClusterCoverage omega n
    let hS := squareDualClusterCoverage_finite omega n hfinite
    FaceBoundaryConnected (squareHoleFill S hS)
      (phb_boundarySupport (squareHoleFill S hS)
        (squareHoleFill_finite S hS)) := by
  dsimp only
  let S := squareDualClusterCoverage omega n
  let hS : S.Finite := squareDualClusterCoverage_finite omega n hfinite
  let K := squareHoleFill S hS
  let hK : K.Finite := squareHoleFill_finite S hS
  have hzeroBox : origin 2 ∈ box 2 n := by
    intro i
    simp [origin]
  have hzeroS : origin 2 ∈ S :=
    box_subset_squareDualClusterCoverage omega n hzeroBox
  have hzeroK : origin 2 ∈ K := subset_squareHoleFill S hS hzeroS
  have hbeaconK : beacon 2 (squareHoleFillRadius S hS) ∉ K := by
    simp [K, squareHoleFill, squareOuterComponent]
  apply faceBoundaryConnected_of_connected_complement K hK hzeroK hbeaconK
  · apply squareHoleFill_inside_connected S hS ⟨origin 2, hzeroS⟩
    intro a b
    exact barrier_reachable_to_induce S a.2 b.2
      (squareDualClusterCoverage_inside_connected omega n a b a.2 b.2)
  · exact squareHoleFill_outside_connected S hS

end

end StatMech.FrontierD
