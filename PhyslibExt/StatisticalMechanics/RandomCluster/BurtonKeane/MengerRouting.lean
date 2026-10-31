/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDisjointWitnesses
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorSidesFromClusters

/-!
# Menger cores and corridor routing

A Menger core, three corridors from neighbours of the origin to three distinct clusters, gives
disjoint routing and the corridor cover of a trifurcation route.

## i. Overview

`MengerCore ω` consists of three neighbours `a_i` of the origin and a finite edge set `G` whose
corridor steps lead from `a_i` to sites `w_i` in three distinct infinite clusters. Corridors to
distinct clusters are disjoint, so the core gives disjoint routing. `MengerRoutingCover d n` asks
for a core in every configuration with three distinct infinite clusters meeting `B_n`.

## ii. Key results

- `StatMech.Walls.bc2_disjoint_of_ne` (in `ThreeDisjointWitnesses`) : corridors to distinct clusters
  are disjoint
- `mng_disjointRouting_of_mengerCore` : a Menger core gives disjoint routing
- `mng_corridorCover_of_mengerCover` : the routing cover gives the corridor cover
- `mng_burton_keane_uniqueness_mengerCover` : uniqueness from the routing cover and a
  configuration-wide trifurcation bound

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}

/-! ## A. Results -/

lemma mng_corridor_mem_destCluster (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {a w : Site d}
    (hc : Relation.ReflTransGen (CorridorStep G) a w) :
    a ∈ cluster d (removeSite 0 (forceOpenFinset G ω)) w := by
  rw [mem_cluster]
  exact (connected_removeSite_forceOpen_of_corridor ω G hc).symm

/-- A Menger core at the origin: three neighbours `a_i` and an edge set `G` whose corridor steps
lead from `a_i` to sites in three pairwise distinct infinite clusters. -/
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

lemma mng_disjointRouting_of_mengerCore (ω : ConfigSpace (Sym2 (Site d)))
    (h : MengerCore ω) : DisjointCorridorRouting ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj,
    ⟨hc1, hc2, hc3⟩, ⟨hw1, hw2, hw3⟩, hd12, hd13, hd23⟩ := h
  set ϱ := removeSite (0 : Site d) (forceOpenFinset G ω) with hϱ
  refine ⟨a₁, a₂, a₃, G, w₁, w₂, w₃,
    cluster d ϱ w₁, cluster d ϱ w₂, cluster d ϱ w₃,
    hne, hadj, ⟨hc1, hc2, hc3⟩, ⟨hw1, hw2, hw3⟩, ?_, ?_, ?_⟩
  · exact ⟨mng_corridor_mem_destCluster ω G hc1,
      mng_corridor_mem_destCluster ω G hc2,
      mng_corridor_mem_destCluster ω G hc3⟩
  · exact ⟨fun u v hu hadj => csc_cluster_adjClosed ϱ w₁ u v hu hadj,
      fun u v hu hadj => csc_cluster_adjClosed ϱ w₂ u v hu hadj,
      fun u v hu hadj => csc_cluster_adjClosed ϱ w₃ u v hu hadj⟩
  · exact ⟨Walls.bc2_disjoint_of_ne hd12,
      Walls.bc2_disjoint_of_ne hd13,
      Walls.bc2_disjoint_of_ne hd23⟩

lemma mng_forceOpenFinset_empty (ω : ConfigSpace (Sym2 (Site d))) :
    forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
  funext e; simp [forceOpenFinset]

lemma mng_mengerCore_of_neighborClusters (ω : ConfigSpace (Sym2 (Site d)))
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

/-- Every configuration with three distinct infinite clusters meeting `B_n` has a Menger core. -/
def MengerRoutingCover (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, MengerCore ω

lemma mng_disjointRouting (d n : ℕ) (hcov : MengerRoutingCover d n) :
    ∀ ω ∈ threeMeetBox d n, DisjointCorridorRouting ω :=
  fun ω hω => mng_disjointRouting_of_mengerCore ω (hcov ω hω)

lemma mng_corridorCover_of_mengerCover {n : ℕ} (hcov : MengerRoutingCover d n) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G :=
  corridorCover_of_routing (fun ω hω => mng_disjointRouting d n hcov ω hω)

/-- Burton–Keane uniqueness from a Menger routing cover. The configuration-wide trifurcation bound
`hbound` together with `hdens` is unsatisfiable when `d ≥ 1` (`tfc_not_hbound_hdens`), so the
statement is vacuous for `d ≥ 1`. -/
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
