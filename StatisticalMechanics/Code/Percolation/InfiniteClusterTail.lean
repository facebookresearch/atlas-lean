/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Code.Percolation.AvoidingAttachment
import Code.Lattice.JordanContour

open Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Percolation

variable {d : ℕ}

abbrev tailClusterVertex (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :=
  {y : Site d // y ∈ cluster d omega x}

abbrev tailClusterGraph (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    SimpleGraph (tailClusterVertex omega x) :=
  (openSubgraph d omega).induce (cluster d omega x)

noncomputable def tailClusterCut (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (K : Finset (Site d)) : Finset (tailClusterVertex omega x) :=
  K.preimage Subtype.val Subtype.val_injective.injOn


noncomputable instance tailClusterGraphLocallyFinite
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    SimpleGraph.LocallyFinite (tailClusterGraph omega x) := by
  intro v
  let f : (tailClusterGraph omega x).neighborSet v ->
      (hypercubicLattice d).neighborSet v.1 := fun w =>
    ⟨w.1.1, (openSubgraph_le omega) w.2⟩
  exact Fintype.ofInjective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (hypercubicLattice d).neighborSet v.1 => (z : Site d)) h)


instance tailClusterGraphPreconnected
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    Fact (tailClusterGraph omega x).Preconnected := ⟨by
  intro u v
  have huv : Connected d omega u.1 v.1 := (Connected.symm u.2).trans v.2
  obtain ⟨w⟩ := huv
  exact StatMech.Lattice.walk_induce_reachable (openSubgraph d omega)
    (cluster d omega x) w (fun z hz => by
      have hzx : z ∈ cluster d omega v.1 := ava_support_mem_cluster omega w hz
      rwa [← cluster_eq_of_connected v.2] at hzx) u.2 v.2⟩


theorem infiniteCluster_component_after_finset
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d)) :
    ∃ D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K),
      D.supp.Infinite := by
  letI : Infinite (tailClusterVertex omega x) := hinf.to_subtype
  let e : (tailClusterGraph omega x).end :=
    ⟨(SimpleGraph.nonempty_ends_of_infinite (tailClusterGraph omega x)).choose,
      (SimpleGraph.nonempty_ends_of_infinite (tailClusterGraph omega x)).choose_spec⟩
  let D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K) :=
    (e : (j : (Finset (tailClusterVertex omega x))ᵒᵖ) →
      (tailClusterGraph omega x).componentComplFunctor.obj j)
      (Opposite.op (tailClusterCut omega x K))
  exact ⟨D, SimpleGraph.end_componentCompl_infinite
    (tailClusterGraph omega x) e (Opposite.op (tailClusterCut omega x K))⟩

def tailComponentSites (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)) :
    Set (Site d) := Subtype.val '' (D : Set (tailClusterVertex omega x))

theorem tailComponentSites_infinite
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K))
    (hD : D.supp.Infinite) : (tailComponentSites omega x K D).Infinite := by
  exact hD.image Subtype.val_injective.injOn

theorem tailComponentSites_subset_cluster
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)) :
    tailComponentSites omega x K D ⊆ cluster d omega x := by
  rintro _ ⟨y, _, rfl⟩
  exact y.2

theorem tailComponentSites_connected_outside
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)) :
    ∀ u ∈ tailComponentSites omega x K D,
      ∀ v ∈ tailComponentSites omega x K D,
        ∃ (hu : u ∉ (K : Set (Site d))) (hv : v ∉ (K : Set (Site d))),
          ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
            ⟨u, hu⟩ ⟨v, hv⟩ := by
  rintro u ⟨uC, huD, rfl⟩ v ⟨vC, hvD, rfl⟩
  rcases huD with ⟨huCut, huComp⟩
  rcases hvD with ⟨hvCut, hvComp⟩
  have huK : uC.1 ∉ (K : Set (Site d)) := by
    intro hmem
    exact huCut (by simp [tailClusterCut, hmem])
  have hvK : vC.1 ∉ (K : Set (Site d)) := by
    intro hmem
    exact hvCut (by simp [tailClusterCut, hmem])
  refine ⟨huK, hvK, ?_⟩
  have hreach :
      ((tailClusterGraph omega x).induce
        ((tailClusterCut omega x K : Set (tailClusterVertex omega x)))ᶜ).Reachable
          ⟨uC, huCut⟩ ⟨vC, hvCut⟩ := by
    rw [← SimpleGraph.ConnectedComponent.eq]
    exact huComp.trans hvComp.symm
  let f0 : {z : tailClusterVertex omega x //
      z ∈ ((tailClusterCut omega x K : Set (tailClusterVertex omega x)))ᶜ} →
      {z : Site d // z ∈ (K : Set (Site d))ᶜ} := fun z =>
    ⟨z.1.1, by
      intro hzK
      exact z.2 (by simp [tailClusterCut, hzK])⟩
  let f : ((tailClusterGraph omega x).induce
      ((tailClusterCut omega x K : Set (tailClusterVertex omega x)))ᶜ) →g
      ((openSubgraph d omega).induce (K : Set (Site d))ᶜ) := {
    toFun := f0
    map_rel' := by
      intro a b hab
      exact hab
  }
  exact hreach.map f




theorem infiniteCluster_has_tail_outside_finset
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d)) :
    ∃ T : Set (Site d), T.Infinite ∧ T ⊆ cluster d omega x ∧
      (∀ u ∈ T, ∀ v ∈ T,
        ∃ (hu : u ∉ (K : Set (Site d))) (hv : v ∉ (K : Set (Site d))),
          ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
            ⟨u, hu⟩ ⟨v, hv⟩) := by
  obtain ⟨D, hD⟩ := infiniteCluster_component_after_finset omega x hinf K
  exact ⟨tailComponentSites omega x K D,
    tailComponentSites_infinite omega x K D hD,
    tailComponentSites_subset_cluster omega x K D,
    tailComponentSites_connected_outside omega x K D⟩




theorem infiniteCluster_has_open_exit_to_infinite_tail
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d))
    (hxK : x ∈ K) :
    ∃ u v : Site d, ∃ T : Set (Site d),
      u ∈ K ∧ v ∉ K ∧ (openSubgraph d omega).Adj u v ∧ v ∈ T ∧
      T.Infinite ∧ T ⊆ cluster d omega x ∧
      (∀ a ∈ T, ∀ b ∈ T,
        ∃ (ha : a ∉ (K : Set (Site d))) (hb : b ∉ (K : Set (Site d))),
          ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
            ⟨a, ha⟩ ⟨b, hb⟩) := by
  obtain ⟨D, hD⟩ := infiniteCluster_component_after_finset omega x hinf K
  have hcut : (tailClusterCut omega x K).Nonempty := by
    refine ⟨⟨x, self_mem_cluster omega x⟩, ?_⟩
    simp [tailClusterCut, hxK]
  obtain ⟨⟨v, u⟩, hvD, huCut, hadj⟩ :=
    D.exists_adj_boundary_pair (tailClusterGraphPreconnected omega x).out hcut
  have huK : u.1 ∈ K := by
    simpa [tailClusterCut] using huCut
  have hvK : v.1 ∉ K := by
    intro hv
    exact D.notMem_of_mem hvD (by simp [tailClusterCut, hv])
  refine ⟨u.1, v.1, tailComponentSites omega x K D,
    huK, hvK, hadj.symm, ⟨v, hvD, rfl⟩, ?_, ?_, ?_⟩
  · exact tailComponentSites_infinite omega x K D hD
  · exact tailComponentSites_subset_cluster omega x K D
  · exact tailComponentSites_connected_outside omega x K D


structure InfiniteClusterTailData (omega : ConfigSpace (Sym2 (Site d)))
    (K : Finset (Site d)) (x : Site d) where
  inside : Site d
  outside : Site d
  tail : Set (Site d)
  inside_mem : inside ∈ K
  outside_not_mem : outside ∉ K
  exit_open : (openSubgraph d omega).Adj inside outside
  outside_mem_tail : outside ∈ tail
  tail_infinite : tail.Infinite
  tail_subset_cluster : tail ⊆ cluster d omega x
  tail_connected_outside :
    ∀ a ∈ tail, ∀ b ∈ tail,
      ∃ (ha : a ∉ (K : Set (Site d))) (hb : b ∉ (K : Set (Site d))),
        ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
          ⟨a, ha⟩ ⟨b, hb⟩


noncomputable def infiniteClusterTailData
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d))
    (hxK : x ∈ K) : InfiniteClusterTailData omega K x := by
  classical
  exact Classical.choice (by
    obtain ⟨u, v, T, hu, hv, huv, hvT, hTinf, hTsub, hTconn⟩ :=
      infiniteCluster_has_open_exit_to_infinite_tail omega x hinf K hxK
    exact ⟨⟨u, v, T, hu, hv, huv, hvT, hTinf, hTsub, hTconn⟩⟩)


theorem disjoint_clusters_of_ne (omega : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hne : cluster d omega x ≠ cluster d omega y) :
    Disjoint (cluster d omega x) (cluster d omega y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact hne ((cluster_eq_of_connected hzx).trans (cluster_eq_of_connected hzy).symm)



theorem threeInfiniteClusters_have_disjoint_tails
    (omega : ConfigSpace (Sym2 (Site d))) (K : Finset (Site d))
    (x1 x2 x3 : Site d)
    (hx1 : x1 ∈ K) (hx2 : x2 ∈ K) (hx3 : x3 ∈ K)
    (hi1 : (cluster d omega x1).Infinite)
    (hi2 : (cluster d omega x2).Infinite)
    (hi3 : (cluster d omega x3).Infinite)
    (hne12 : cluster d omega x1 ≠ cluster d omega x2)
    (hne13 : cluster d omega x1 ≠ cluster d omega x3)
    (hne23 : cluster d omega x2 ≠ cluster d omega x3) :
    ∃ D1 : InfiniteClusterTailData omega K x1,
      ∃ D2 : InfiniteClusterTailData omega K x2,
        ∃ D3 : InfiniteClusterTailData omega K x3,
          Disjoint D1.tail D2.tail ∧ Disjoint D1.tail D3.tail ∧
            Disjoint D2.tail D3.tail := by
  let D1 := infiniteClusterTailData omega x1 hi1 K hx1
  let D2 := infiniteClusterTailData omega x2 hi2 K hx2
  let D3 := infiniteClusterTailData omega x3 hi3 K hx3
  have hc12 := disjoint_clusters_of_ne omega hne12
  have hc13 := disjoint_clusters_of_ne omega hne13
  have hc23 := disjoint_clusters_of_ne omega hne23
  exact ⟨D1, D2, D3,
    hc12.mono D1.tail_subset_cluster D2.tail_subset_cluster,
    hc13.mono D1.tail_subset_cluster D3.tail_subset_cluster,
    hc23.mono D2.tail_subset_cluster D3.tail_subset_cluster⟩

end StatMech.Percolation
