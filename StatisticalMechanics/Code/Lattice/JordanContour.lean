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
import Code.Lattice.CrossingParity
import Code.Lattice.UniqueInfiniteComponent

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}










theorem walk_induce_reachable {V : Type*} (G : SimpleGraph V) (s : Set V)
    {x y : V} (w : G.Walk x y) (hw : ∀ z ∈ w.support, z ∈ s)
    (hx : x ∈ s) (hy : y ∈ s) : (G.induce s).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    have hb : b ∈ s := hw b (by simp)
    exact ((show (G.induce s).Adj ⟨a, hx⟩ ⟨b, hb⟩ from hab).reachable).trans
      (ih (fun z hz => hw z (by simp [hz])) hb hy)









theorem latticeMinusBarrier_adj_of_both_mem (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hx : x ∈ S) (hy : y ∈ S) :
    (latticeMinusBarrier S).Adj x y :=
  ⟨hadj, by rw [bdEdge_mk]; tauto⟩


theorem latticeMinusBarrier_adj_of_both_not_mem (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hx : x ∉ S) (hy : y ∉ S) :
    (latticeMinusBarrier S).Adj x y :=
  ⟨hadj, by rw [bdEdge_mk]; tauto⟩










theorem openWalk_support_mem_cluster (o : Site 2) {y : Site 2}
    (w : (openSubgraph 2 ω).Walk o y) : ∀ z ∈ w.support, z ∈ cluster 2 ω o :=
  fun z hz => (w.takeUntil z hz).reachable



noncomputable def clusterOpenToBarrierHom (o : Site 2) :
    (openSubgraph 2 ω).induce (cluster 2 ω o) →g latticeMinusBarrier (cluster 2 ω o) where
  toFun v := (v : Site 2)
  map_rel' := by
    intro a b hab
    have hopen : IsOpenEdge 2 ω (a : Site 2) (b : Site 2) := hab
    exact latticeMinusBarrier_adj_of_both_mem _ hopen.1 a.2 b.2






theorem cluster_reachable_in_barrier (o : Site 2) {x y : Site 2}
    (hx : x ∈ cluster 2 ω o) (hy : y ∈ cluster 2 ω o) :
    (latticeMinusBarrier (cluster 2 ω o)).Reachable x y := by
  obtain ⟨wx⟩ := (mem_cluster.mp hx)
  obtain ⟨wy⟩ := (mem_cluster.mp hy)
  have rx := walk_induce_reachable (openSubgraph 2 ω) (cluster 2 ω o) wx
    (openWalk_support_mem_cluster o wx) (self_mem_cluster ω o) hx
  have ry := walk_induce_reachable (openSubgraph 2 ω) (cluster 2 ω o) wy
    (openWalk_support_mem_cluster o wy) (self_mem_cluster ω o) hy
  have hmap := (rx.symm.trans ry).map (clusterOpenToBarrierHom (ω := ω) o)
  simpa [clusterOpenToBarrierHom] using hmap





theorem insideComponent_supp_subset_cluster (o : Site 2) :
    ((latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o).supp ⊆ cluster 2 ω o := by
  intro z hz
  rw [ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq] at hz
  obtain ⟨w⟩ := hz
  exact (latticeMinusBarrier_sameSide (cluster 2 ω o) w).mpr (self_mem_cluster ω o)


theorem insideComponent_finite (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ((latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o).supp.Finite :=
  hfin.subset (insideComponent_supp_subset_cluster (ω := ω) o)











noncomputable def extToBarrierHom (K : Set (Site 2)) (R : ℕ) (hsub : exterior 2 R ⊆ Kᶜ) :
    (hypercubicLattice 2).induce (exterior 2 R) →g latticeMinusBarrier K where
  toFun v := (v : Site 2)
  map_rel' := by
    intro a b hab
    exact latticeMinusBarrier_adj_of_both_not_mem _ hab (hsub a.2) (hsub b.2)






theorem exterior_reachable_in_barrier (K : Set (Site 2)) (R : ℕ) (hK : K ⊆ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    (latticeMinusBarrier K).Reachable x y := by
  have hsub : exterior 2 R ⊆ Kᶜ := exterior_subset_compl K R hK
  have hmap := (box_exterior_connected R (by norm_num) x y hx hy).map (extToBarrierHom K R hsub)
  simpa [extToBarrierHom] using hmap




theorem outsideComponent_infinite (K : Set (Site 2)) (R : ℕ) (hK : K ⊆ box 2 R) :
    ((latticeMinusBarrier K).connectedComponentMk (beacon 2 R)).supp.Infinite := by
  have hbe : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have : Infinite ↥(exterior 2 R) := (exterior_infinite R (by norm_num)).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior 2 R) => ((w : Site 2))) ?_ ?_
  · intro a b hab; exact Subtype.ext hab
  · intro w
    rw [ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact exterior_reachable_in_barrier K R hK w.2 hbe










theorem cluster_inside_not_reachable_outside (o : Site 2) {x y : Site 2}
    (hx : x ∈ cluster 2 ω o) (hy : y ∉ cluster 2 ω o) :
    ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable x y :=
  not_reachable_latticeMinusBarrier (cluster 2 ω o) hx hy





theorem inside_ne_outside_component (o : Site 2) (R : ℕ) (hR : cluster 2 ω o ⊆ box 2 R) :
    (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o ≠
      (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk (beacon 2 R) := by
  intro h
  rw [SimpleGraph.ConnectedComponent.eq] at h
  have hbe : beacon 2 R ∉ cluster 2 ω o := by
    have : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
    exact (exterior_subset_compl (cluster 2 ω o) R hR) this
  exact not_reachable_latticeMinusBarrier (cluster 2 ω o) (self_mem_cluster ω o) hbe h











theorem barrier_sameSide_of_reachable (S : Set (Site 2)) {x y : Site 2}
    (h : (latticeMinusBarrier S).Reachable x y) : (x ∈ S ↔ y ∈ S) := by
  obtain ⟨w⟩ := h
  exact latticeMinusBarrier_sameSide S w





theorem barrier_separates (S : Set (Site 2)) :
    (∀ ⦃x y : Site 2⦄, (latticeMinusBarrier S).Reachable x y → (x ∈ S ↔ y ∈ S)) ∧
      (∀ ⦃x y : Site 2⦄, x ∈ S → y ∉ S → ¬ (latticeMinusBarrier S).Reachable x y) :=
  ⟨fun _ _ h => barrier_sameSide_of_reachable S h,
   fun _ _ hx hy => not_reachable_latticeMinusBarrier S hx hy⟩



















theorem discrete_jordan_separation (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ R : ℕ, cluster 2 ω o ⊆ box 2 R ∧
      (∀ ⦃x y : Site 2⦄, x ∈ cluster 2 ω o → y ∈ cluster 2 ω o →
        (latticeMinusBarrier (cluster 2 ω o)).Reachable x y) ∧
      (∀ ⦃x y : Site 2⦄, x ∈ exterior 2 R → y ∈ exterior 2 R →
        (latticeMinusBarrier (cluster 2 ω o)).Reachable x y) ∧
      (∀ ⦃x y : Site 2⦄, x ∈ cluster 2 ω o → y ∉ cluster 2 ω o →
        ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable x y) := by
  obtain ⟨R, hR⟩ := finite_subset_box (cluster 2 ω o) hfin
  exact ⟨R, hR,
    fun _ _ hx hy => cluster_reachable_in_barrier o hx hy,
    fun _ _ hx hy => exterior_reachable_in_barrier _ R hR hx hy,
    fun _ _ hx hy => not_reachable_latticeMinusBarrier _ hx hy⟩













theorem discrete_jordan_components (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ (R : ℕ)
      (_ : cluster 2 ω o ⊆ box 2 R)
      (Cin Cout : (latticeMinusBarrier (cluster 2 ω o)).ConnectedComponent),
      Cin = (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o ∧
      Cout = (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk (beacon 2 R) ∧
      Cin.supp.Finite ∧ Cout.supp.Infinite ∧ Cin ≠ Cout ∧
      cluster 2 ω o ⊆ Cin.supp ∧ exterior 2 R ⊆ Cout.supp := by
  obtain ⟨R, hR⟩ := finite_subset_box (cluster 2 ω o) hfin
  refine ⟨R, hR,
    (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o,
    (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk (beacon 2 R),
    rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · 
    exact hfin.subset (insideComponent_supp_subset_cluster (ω := ω) o)
  · 
    exact outsideComponent_infinite (cluster 2 ω o) R hR
  · 
    exact inside_ne_outside_component (ω := ω) o R hR
  · 
    intro z hz
    rw [ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact cluster_reachable_in_barrier o hz (self_mem_cluster ω o)
  · 
    intro z hz
    have hbe : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
    rw [ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact exterior_reachable_in_barrier (cluster 2 ω o) R hR hz hbe
































end Lattice

end StatMech
