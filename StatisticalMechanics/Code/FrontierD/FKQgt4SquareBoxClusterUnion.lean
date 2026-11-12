/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareHoleFill
import Code.FrontierB.BoxGraphPath

open Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.ConfigSpace
open StatMech.FrontierB

noncomputable section


def squareBoxClusterUnion (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat) :
    Set (Site 2) :=
  ⋃ x ∈ box 2 n, cluster 2 omega x

theorem mem_squareBoxClusterUnion_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat) (y : Site 2) :
    y ∈ squareBoxClusterUnion omega n ↔
      ∃ x ∈ box 2 n, y ∈ cluster 2 omega x := by
  simp [squareBoxClusterUnion]


theorem box_subset_squareBoxClusterUnion
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat) :
    box 2 n ⊆ squareBoxClusterUnion omega n := by
  intro x hx
  exact (mem_squareBoxClusterUnion_iff omega n x).2
    ⟨x, hx, self_mem_cluster omega x⟩


theorem squareBoxClusterUnion_finite
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x ∈ box 2 n, (cluster 2 omega x).Finite) :
    (squareBoxClusterUnion omega n).Finite := by
  exact Set.Finite.biUnion (box_finite 2 n) hfinite

private theorem cluster_walk_reachable_in_squareBoxClusterUnion
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    {x y : Site 2} (hx : x ∈ box 2 n) (hy : y ∈ cluster 2 omega x) :
    ((hypercubicLattice 2).induce (squareBoxClusterUnion omega n)).Reachable
      ⟨x, box_subset_squareBoxClusterUnion omega n hx⟩
      ⟨y, (mem_squareBoxClusterUnion_iff omega n y).2 ⟨x, hx, hy⟩⟩ := by
  obtain ⟨w⟩ := mem_cluster.mp hy
  let wl : (hypercubicLattice 2).Walk x y :=
    w.map (Hom.ofLE (openSubgraph_le omega))
  have hsupport : ∀ z ∈ wl.support, z ∈ squareBoxClusterUnion omega n := by
    intro z hz
    have hz' : z ∈ w.support := by
      change z ∈ (w.map (Hom.ofLE (openSubgraph_le omega))).support at hz
      rw [Walk.support_map] at hz
      obtain ⟨u, hu, huz⟩ := List.mem_map.mp hz
      simpa only using huz ▸ hu
    exact (mem_squareBoxClusterUnion_iff omega n z).2
      ⟨x, hx, openWalk_support_mem_cluster x w z hz'⟩
  exact walk_induce_reachable (hypercubicLattice 2)
    (squareBoxClusterUnion omega n) wl hsupport
    (box_subset_squareBoxClusterUnion omega n hx)
    ((mem_squareBoxClusterUnion_iff omega n y).2 ⟨x, hx, hy⟩)

private theorem box_walk_reachable_in_squareBoxClusterUnion
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    {x y : Site 2} (hx : x ∈ box 2 n) (hy : y ∈ box 2 n) :
    ((hypercubicLattice 2).induce (squareBoxClusterUnion omega n)).Reachable
      ⟨x, box_subset_squareBoxClusterUnion omega n hx⟩
      ⟨y, box_subset_squareBoxClusterUnion omega n hy⟩ := by
  obtain ⟨w⟩ := boxGraph_preconnected 2 n ⟨x, hx⟩ ⟨y, hy⟩
  let incl : (hypercubicLattice 2).induce (box 2 n) →g hypercubicLattice 2 :=
    { toFun := Subtype.val
      map_rel' := fun {a b} h => h }
  let wl := w.map incl
  have hsupport : ∀ z ∈ wl.support, z ∈ squareBoxClusterUnion omega n := by
    intro z hz
    rw [Walk.support_map] at hz
    obtain ⟨u, hu, huz⟩ := List.mem_map.mp hz
    subst z
    simpa [incl] using box_subset_squareBoxClusterUnion omega n u.2
  simpa [wl, incl] using walk_induce_reachable (hypercubicLattice 2)
    (squareBoxClusterUnion omega n) wl hsupport
    (box_subset_squareBoxClusterUnion omega n hx)
    (box_subset_squareBoxClusterUnion omega n hy)



theorem squareBoxClusterUnion_connected
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat) :
    ∀ a b : squareBoxClusterUnion omega n,
      ((hypercubicLattice 2).induce (squareBoxClusterUnion omega n)).Reachable a b := by
  intro a b
  obtain ⟨x, hxbox, hxa⟩ :=
    (mem_squareBoxClusterUnion_iff omega n a).1 a.2
  obtain ⟨y, hybox, hyb⟩ :=
    (mem_squareBoxClusterUnion_iff omega n b).1 b.2
  have hxa' := cluster_walk_reachable_in_squareBoxClusterUnion
    omega n hxbox hxa
  have hxy := box_walk_reachable_in_squareBoxClusterUnion
    omega n hxbox hybox
  have hyb' := cluster_walk_reachable_in_squareBoxClusterUnion
    omega n hybox hyb
  simpa using hxa'.symm.trans (hxy.trans hyb')



theorem squareBoxClusterUnion_fill_boundary_connected
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x ∈ box 2 n, (cluster 2 omega x).Finite) :
    FaceBoundaryConnected
      (squareHoleFill (squareBoxClusterUnion omega n)
        (squareBoxClusterUnion_finite omega n hfinite))
      (phb_boundarySupport
        (squareHoleFill (squareBoxClusterUnion omega n)
          (squareBoxClusterUnion_finite omega n hfinite))
        (squareHoleFill_finite (squareBoxClusterUnion omega n)
          (squareBoxClusterUnion_finite omega n hfinite))) := by
  apply squareHoleFill_faceBoundaryConnected
  · exact ⟨(0 : Site 2),
      box_subset_squareBoxClusterUnion omega n (by simp [box])⟩
  · exact squareBoxClusterUnion_connected omega n

end

end StatMech.FrontierD
