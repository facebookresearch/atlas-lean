/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Percolation.HrouteDisjointPaths
import Code.Percolation.HrouteHighDim

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}













theorem mng_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (w : Site d)
    {u v : Site d} (hu : u ∈ cluster d ϱ w) (hadj : (openSubgraph d ϱ).Adj u v) :
    v ∈ cluster d ϱ w := by
  rw [mem_cluster] at hu ⊢
  exact hu.trans hadj.reachable





theorem mng_corridor_mem_destCluster (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {a w : Site d}
    (hc : Relation.ReflTransGen (CorridorStep G) a w) :
    a ∈ cluster d (removeSite 0 (forceOpenFinset G ω)) w := by
  rw [mem_cluster]
  exact (connected_removeSite_forceOpen_of_corridor ω G hc).symm




theorem mng_disjoint_of_cluster_ne (ϱ : ConfigSpace (Sym2 (Site d))) (w₁ w₂ : Site d)
    (h : cluster d ϱ w₁ ≠ cluster d ϱ w₂) :
    Disjoint (cluster d ϱ w₁) (cluster d ϱ w₂) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  rw [mem_cluster] at hz1 hz2
  exact h (cluster_eq_of_connected (hz1.trans hz2.symm))

















def MengerCore (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) (w₁ w₂ w₃ : Site d),
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    (Relation.ReflTransGen (CorridorStep G) a₁ w₁ ∧
      Relation.ReflTransGen (CorridorStep G) a₂ w₂ ∧
      Relation.ReflTransGen (CorridorStep G) a₃ w₃) ∧
    ((cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite) ∧
    (cluster d (removeSite 0 (forceOpenFinset G ω)) w₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₂ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) w₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₃ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) w₂
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₃)















theorem mng_disjointRouting_of_mengerCore (ω : ConfigSpace (Sym2 (Site d)))
    (h : MengerCore ω) : DisjointCorridorRouting ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj,
    ⟨hc1, hc2, hc3⟩, ⟨hw1, hw2, hw3⟩, hd12, hd13, hd23⟩ := h
  set ϱ := removeSite (0 : Site d) (forceOpenFinset G ω) with hϱ
  
  refine ⟨a₁, a₂, a₃, G, w₁, w₂, w₃,
    cluster d ϱ w₁, cluster d ϱ w₂, cluster d ϱ w₃,
    hne, hadj, ⟨hc1, hc2, hc3⟩, ⟨hw1, hw2, hw3⟩, ?_, ?_, ?_⟩
  · 
    exact ⟨mng_corridor_mem_destCluster ω G hc1,
      mng_corridor_mem_destCluster ω G hc2,
      mng_corridor_mem_destCluster ω G hc3⟩
  · 
    exact ⟨fun u v hu hadj => mng_cluster_adjClosed ϱ w₁ hu hadj,
      fun u v hu hadj => mng_cluster_adjClosed ϱ w₂ hu hadj,
      fun u v hu hadj => mng_cluster_adjClosed ϱ w₃ hu hadj⟩
  · 
    exact ⟨mng_disjoint_of_cluster_ne ϱ w₁ w₂ hd12,
      mng_disjoint_of_cluster_ne ϱ w₁ w₃ hd13,
      mng_disjoint_of_cluster_ne ϱ w₂ w₃ hd23⟩











theorem mng_forceOpenFinset_empty (ω : ConfigSpace (Sym2 (Site d))) :
    forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
  funext e; simp [forceOpenFinset]











theorem mng_mengerCore_of_neighborClusters (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite)
    (hdist : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    MengerCore ω := by
  refine ⟨a₁, a₂, a₃, ∅, a₁, a₂, a₃, hne, hadj,
    ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩,
    ?_, ?_⟩
  · rw [mng_forceOpenFinset_empty]; exact hinf
  · rw [mng_forceOpenFinset_empty]; exact hdist













def MengerRoutingCover (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, MengerCore ω





theorem mng_disjointRouting (d n : ℕ) (hcov : MengerRoutingCover d n) :
    ∀ ω ∈ threeMeetBox d n, DisjointCorridorRouting ω :=
  fun ω hω => mng_disjointRouting_of_mengerCore ω (hcov ω hω)




theorem mng_corridorCover_of_mengerCover {n : ℕ} (hcov : MengerRoutingCover d n) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G :=
  corridorCover_of_routing (fun ω hω => mng_disjointRouting d n hcov ω hω)




















theorem mng_burton_keane_uniqueness_mengerCover
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hcov : ∀ n : ℕ, MengerRoutingCover d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_corridorCover μ herg hfe bdry hbound hvol hdens
    (fun n => mng_corridorCover_of_mengerCover (hcov n))

end DisjointPaths

end Percolation

end StatMech
