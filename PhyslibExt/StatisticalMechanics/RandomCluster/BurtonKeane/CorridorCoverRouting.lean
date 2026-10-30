/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationConstruction

/-!
# Corridor covers and the route

Forced corridors that route three neighbours of the origin to separated infinite clusters give
neighbour trifurcation precursors; covering the three-clusters event by them gives the route for
measures with finite energy.

## i. Overview

An open edge avoiding the origin survives removing it after forcing, and so do corridor chains.
`CorridorWorks a G` is the event that forcing `G` connects the neighbours `a i` of the origin by
corridors to three separated infinite clusters; it lies in the preimage of a neighbour trifurcation
precursor. Separation follows from disjoint closed regions. `CorridorStep G` is one step of a
corridor along `G` avoiding the origin. Precursors are measurable, so a countable cover of
`threeMeetBox d n` by corridor events gives, with finite energy, the route.
`DisjointCorridorRouting ω` packages corridors into three disjoint closed regions and gives such
covers.

**Fidelity.** `burton_keane_uniqueness_corridorCover` and `burton_keane_uniqueness_disjointRouting`
also assume the counting hypotheses of `burton_keane_uniqueness_full`, which are unsatisfiable for
`d ≥ 1` (`tfc_not_hbound_hdens`), so they have content only for `d = 0`.

## ii. Key results

- `corridorWorks_subset_force_precursor` : corridor events lie in forced precursors.
- `hroute_of_corridorCover` : the route from corridor covers.

## iii. Table of contents

- A. Corridors after forcing
- B. Corridor events
- C. Measurability and the route
- D. Disjoint corridor routing

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}

/-! ## A. Corridors after forcing -/

lemma isOpenEdge_removeSite_forceOpen_step (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y) (hmem : s(x, y) ∈ G)
    (h0 : (0 : Site d) ∉ s(x, y)) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y := by
  refine ⟨hadj, ?_⟩
  rw [removeSite_apply_of_notMem h0]
  exact forceOpenFinset_of_mem hmem ω

lemma connected_removeSite_forceOpen_of_corridor (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {p q : Site d}
    (h : Relation.ReflTransGen
      (fun u v => (hypercubicLattice d).Adj u v ∧ s(u, v) ∈ G ∧ (0 : Site d) ∉ s(u, v)) p q) :
    Connected d (removeSite 0 (forceOpenFinset G ω)) p q := by
  induction h with
  | refl => exact connected_rfl
  | tail _ hstep ih =>
    obtain ⟨hadj, hmem, h0⟩ := hstep
    exact ih.trans (IsOpenEdge.connected (isOpenEdge_removeSite_forceOpen_step ω G hadj hmem h0))

/-! ## B. Corridor events -/

/-- The event that forcing `G` routes the three distinct neighbours `a i` of the origin along
corridors
to sites whose cut clusters are infinite and pairwise separated. -/
def CorridorWorks (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    ((cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite) ∧
    (cluster d (removeSite 0 (forceOpenFinset G ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₂ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) a₂
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃)}

lemma corridorWorks_subset_force_precursor (a₁ a₂ a₃ : Site d)
    (G : Finset (Sym2 (Site d))) :
    CorridorWorks a₁ a₂ a₃ G ⊆
      (fun ω => forceOpenFinset G ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃ := by
  rintro ω ⟨hne, hadj, hinf, hd12, hd13, hd23⟩
  refine ⟨hne, hadj, hinf, ?_, ?_, ?_⟩
  · intro hc; exact hd12 (cluster_eq_of_connected hc)
  · intro hc; exact hd13 (cluster_eq_of_connected hc)
  · intro hc; exact hd23 (cluster_eq_of_connected hc)

lemma cluster_subset_of_adjClosed (ϱ : ConfigSpace (Sym2 (Site d)))
    (S : Set (Site d)) (a : Site d) (ha : a ∈ S)
    (hclosed : ∀ u v, u ∈ S → (openSubgraph d ϱ).Adj u v → v ∈ S) :
    cluster d ϱ a ⊆ S := by
  intro y hy
  rw [mem_cluster] at hy
  unfold Connected at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact ha
  | @tail b c _ hbc ih => exact hclosed b c ih hbc

lemma cluster_ne_of_disjoint (ϱ : ConfigSpace (Sym2 (Site d))) (a b : Site d)
    (S T : Set (Site d)) (hS : cluster d ϱ a ⊆ S) (hT : cluster d ϱ b ⊆ T)
    (hdisj : Disjoint S T) : cluster d ϱ a ≠ cluster d ϱ b := by
  intro heq
  have ha : a ∈ cluster d ϱ a := self_mem_cluster ϱ a
  have ha' : a ∈ cluster d ϱ b := heq ▸ ha
  have hmem : a ∈ S ∩ T := ⟨hS ha, hT ha'⟩
  rw [Set.disjoint_iff_inter_eq_empty] at hdisj
  rw [hdisj] at hmem
  exact absurd hmem (Set.notMem_empty a)

lemma corridorWorks_of_separated (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d)))
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (S₁ S₂ S₃ : Set (Site d))
    (hmem₁ : a₁ ∈ S₁) (hmem₂ : a₂ ∈ S₂) (hmem₃ : a₃ ∈ S₃)
    (hcl₁ : ∀ u v, u ∈ S₁ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₁)
    (hcl₂ : ∀ u v, u ∈ S₂ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₂)
    (hcl₃ : ∀ u v, u ∈ S₃ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₃)
    (hd12 : Disjoint S₁ S₂) (hd13 : Disjoint S₁ S₃) (hd23 : Disjoint S₂ S₃)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite) :
    ω ∈ CorridorWorks a₁ a₂ a₃ G := by
  set ϱ := removeSite 0 (forceOpenFinset G ω) with hϱ
  have hsub₁ : cluster d ϱ a₁ ⊆ S₁ := cluster_subset_of_adjClosed ϱ S₁ a₁ hmem₁ hcl₁
  have hsub₂ : cluster d ϱ a₂ ⊆ S₂ := cluster_subset_of_adjClosed ϱ S₂ a₂ hmem₂ hcl₂
  have hsub₃ : cluster d ϱ a₃ ⊆ S₃ := cluster_subset_of_adjClosed ϱ S₃ a₃ hmem₃ hcl₃
  exact ⟨hne, hadj, hinf,
    cluster_ne_of_disjoint ϱ a₁ a₂ S₁ S₂ hsub₁ hsub₂ hd12,
    cluster_ne_of_disjoint ϱ a₁ a₃ S₁ S₃ hsub₁ hsub₃ hd13,
    cluster_ne_of_disjoint ϱ a₂ a₃ S₂ S₃ hsub₂ hsub₃ hd23⟩

/-- One corridor step: a lattice edge of `G` not containing the origin. -/
abbrev CorridorStep (G : Finset (Sym2 (Site d))) (u v : Site d) : Prop :=
  (hypercubicLattice d).Adj u v ∧ s(u, v) ∈ G ∧ (0 : Site d) ∉ s(u, v)

lemma corridorWorks_of_corridors (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d)))
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (w₁ w₂ w₃ : Site d)
    (hcor₁ : Relation.ReflTransGen (CorridorStep G) a₁ w₁)
    (hcor₂ : Relation.ReflTransGen (CorridorStep G) a₂ w₂)
    (hcor₃ : Relation.ReflTransGen (CorridorStep G) a₃ w₃)
    (hw₁ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite)
    (hw₂ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite)
    (hw₃ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite)
    (S₁ S₂ S₃ : Set (Site d))
    (hmem₁ : a₁ ∈ S₁) (hmem₂ : a₂ ∈ S₂) (hmem₃ : a₃ ∈ S₃)
    (hcl₁ : ∀ u v, u ∈ S₁ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₁)
    (hcl₂ : ∀ u v, u ∈ S₂ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₂)
    (hcl₃ : ∀ u v, u ∈ S₃ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₃)
    (hd12 : Disjoint S₁ S₂) (hd13 : Disjoint S₁ S₃) (hd23 : Disjoint S₂ S₃) :
    ω ∈ CorridorWorks a₁ a₂ a₃ G := by
  have hinf₁ : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite := by
    rw [cluster_eq_of_connected (connected_removeSite_forceOpen_of_corridor ω G hcor₁)]; exact hw₁
  have hinf₂ : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite := by
    rw [cluster_eq_of_connected (connected_removeSite_forceOpen_of_corridor ω G hcor₂)]; exact hw₂
  have hinf₃ : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite := by
    rw [cluster_eq_of_connected (connected_removeSite_forceOpen_of_corridor ω G hcor₃)]; exact hw₃
  exact corridorWorks_of_separated ω a₁ a₂ a₃ G hne hadj S₁ S₂ S₃ hmem₁ hmem₂ hmem₃
    hcl₁ hcl₂ hcl₃ hd12 hd13 hd23 ⟨hinf₁, hinf₂, hinf₃⟩

/-! ## C. Measurability and the route -/

lemma measurableSet_clusterInfinite_removeSite (x a : Site d) :
    MeasurableSet
      {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite}
      = (fun ω => removeSite x ω) ⁻¹' {ω' | (cluster d ω' a).Infinite} := rfl
  rw [h]
  exact (measurable_removeSite x) (measurableSet_clusterInfinite a)

lemma measurableSet_neighborTrifPrecursor (a₁ a₂ a₃ : Site d) :
    MeasurableSet (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  classical
  have heq : NeighborTrifPrecursor d a₁ a₂ a₃
      = (if (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
            ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
              (hypercubicLattice d).Adj 0 a₃) then Set.univ else ∅)
        ∩ ({ω | (cluster d (removeSite 0 ω) a₁).Infinite}
            ∩ {ω | (cluster d (removeSite 0 ω) a₂).Infinite}
            ∩ {ω | (cluster d (removeSite 0 ω) a₃).Infinite})
        ∩ ({ω | ¬ Connected d (removeSite 0 ω) a₁ a₂}
            ∩ {ω | ¬ Connected d (removeSite 0 ω) a₁ a₃}
            ∩ {ω | ¬ Connected d (removeSite 0 ω) a₂ a₃}) := by
    ext ω
    simp only [NeighborTrifPrecursor, Set.mem_ofPred_eq, Set.mem_inter_iff]
    by_cases hh : (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
          (hypercubicLattice d).Adj 0 a₃)
    · simp only [ite_eq_left hh, Set.mem_univ, true_and]
      constructor
      · rintro ⟨_, _, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
        exact ⟨⟨⟨hi1, hi2⟩, hi3⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩
      · rintro ⟨⟨⟨hi1, hi2⟩, hi3⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩
        exact ⟨hh.1, hh.2, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
    · simp only [ite_eq_right hh, Set.mem_empty_iff_false, false_and, iff_false]
      rintro ⟨hne, hadj, _, _⟩
      exact hh ⟨hne, hadj⟩
  rw [heq]
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · by_cases hh : (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
          (hypercubicLattice d).Adj 0 a₃)
    · rw [ite_eq_left hh]; exact MeasurableSet.univ
    · rw [ite_eq_right hh]; exact MeasurableSet.empty
  · exact ((measurableSet_clusterInfinite_removeSite 0 a₁).inter
      (measurableSet_clusterInfinite_removeSite 0 a₂)).inter
      (measurableSet_clusterInfinite_removeSite 0 a₃)
  · exact (((measurableSet_connected_removeSite 0 a₁ a₂).compl).inter
      ((measurableSet_connected_removeSite 0 a₁ a₃).compl)).inter
      ((measurableSet_connected_removeSite 0 a₂ a₃).compl)

lemma exists_pos_of_cover {ι : Type*} [Countable ι]
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {A : Set (ConfigSpace (Sym2 (Site d)))} {B : ι → Set (ConfigSpace (Sym2 (Site d)))}
    (hsub : A ⊆ ⋃ i, B i) (hApos : 0 < μ A) : ∃ i, 0 < μ (B i) := by
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : μ (⋃ i, B i) = 0 := by
    refine le_antisymm ?_ bot_le
    have hsum : μ (⋃ i, B i) ≤ ∑' i, μ (B i) := measure_iUnion_le B
    have hz : ∑' i, μ (B i) = 0 := by simp [hcon]
    rw [hz] at hsum; exact hsum
  have hle : μ A ≤ μ (⋃ i, B i) := measure_mono hsub
  rw [hunion0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hApos)

lemma pos_of_forceOpen_preimage
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (G : Finset (Sym2 (Site d)))
    {A B : Set (ConfigSpace (Sym2 (Site d)))} (hmB : MeasurableSet B)
    (hsub : A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' B) (hApos : 0 < μ A) :
    0 < μ B := by
  by_contra h
  rw [not_lt, nonpos_iff_eq_zero] at h
  have hac := hfe G
  have hpush : (μ.map (fun ω => forceOpenFinset G ω)) B
      = μ ((fun ω => forceOpenFinset G ω) ⁻¹' B) :=
    Measure.map_apply (measurable_forceOpenFinset G) hmB
  have hpre0 : μ ((fun ω => forceOpenFinset G ω) ⁻¹' B) = 0 := by rw [← hpush]; exact hac h
  have hle : μ A ≤ μ ((fun ω => forceOpenFinset G ω) ⁻¹' B) := measure_mono hsub
  rw [hpre0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hApos)

lemma hroute_at_of_corridorCover
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) {n : ℕ}
    (hcorr : threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G)
    (hpos : 0 < μ (threeMeetBox d n)) :
    ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  classical
  set ι := Site d × Site d × Site d × Finset (Sym2 (Site d)) with hι
  set B : ι → Set (ConfigSpace (Sym2 (Site d))) :=
    fun p => CorridorWorks p.1 p.2.1 p.2.2.1 p.2.2.2 with hB
  have hcover : threeMeetBox d n ⊆ ⋃ p : ι, B p := by
    intro ω hω
    obtain ⟨a₁, a₂, a₃, G, hmem⟩ := by
      have := hcorr hω
      simpa only [Set.mem_iUnion] using this
    exact Set.mem_iUnion.mpr ⟨(a₁, a₂, a₃, G), hmem⟩
  obtain ⟨p, hppos⟩ := exists_pos_of_cover μ hcover hpos
  obtain ⟨a₁, a₂, a₃, G⟩ := p
  refine ⟨a₁, a₂, a₃, ?_⟩
  exact pos_of_forceOpen_preimage μ hfe G
    (measurableSet_neighborTrifPrecursor a₁ a₂ a₃)
    (corridorWorks_subset_force_precursor a₁ a₂ a₃ G) hppos

lemma hroute_of_corridorCover
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hcorr : ∀ n : ℕ, threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  fun n hpos => hroute_at_of_corridorCover μ hfe (hcorr n) hpos

/-! ## D. Disjoint corridor routing -/

/-- Disjoint corridor routing: three neighbours of the origin, a forced edge set and three disjoint
regions closed under open and forced edges, with each neighbour routed inside its region to an
infinite cut cluster. -/
def DisjointCorridorRouting (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) (w₁ w₂ w₃ : Site d)
    (S₁ S₂ S₃ : Set (Site d)),
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    (Relation.ReflTransGen (CorridorStep G) a₁ w₁ ∧
      Relation.ReflTransGen (CorridorStep G) a₂ w₂ ∧
      Relation.ReflTransGen (CorridorStep G) a₃ w₃) ∧
    ((cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite) ∧
    (a₁ ∈ S₁ ∧ a₂ ∈ S₂ ∧ a₃ ∈ S₃) ∧
    ((∀ u v, u ∈ S₁ →
        (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₁) ∧
      (∀ u v, u ∈ S₂ →
        (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₂) ∧
      (∀ u v, u ∈ S₃ →
        (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₃)) ∧
    (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃)

lemma corridorCover_of_routing {n : ℕ}
    (hroute : ∀ ω ∈ threeMeetBox d n, DisjointCorridorRouting ω) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G := by
  intro ω hω
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, S₁, S₂, S₃, hne, hadj, ⟨hc1, hc2, hc3⟩,
    ⟨hw1, hw2, hw3⟩, ⟨hm1, hm2, hm3⟩, ⟨hcl1, hcl2, hcl3⟩, ⟨hd12, hd13, hd23⟩⟩ := hroute ω hω
  have hworks : ω ∈ CorridorWorks a₁ a₂ a₃ G :=
    corridorWorks_of_corridors ω a₁ a₂ a₃ G hne hadj w₁ w₂ w₃ hc1 hc2 hc3 hw1 hw2 hw3
      S₁ S₂ S₃ hm1 hm2 hm3 hcl1 hcl2 hcl3 hd12 hd13 hd23
  simp only [Set.mem_iUnion]
  exact ⟨a₁, a₂, a₃, G, hworks⟩

/-- Burton–Keane conclusion from corridor covers of every box and the counting hypotheses of
`burton_keane_uniqueness_full`. Those hypotheses are unsatisfiable for `d ≥ 1`
(`tfc_not_hbound_hdens`), so the statement has content only for `d = 0`. -/
lemma burton_keane_uniqueness_corridorCover
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hcorr : ∀ n : ℕ, threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_trif_route μ herg hfe bdry hbound hvol hdens
    (hroute_of_corridorCover μ hfe hcorr)

/-- Burton–Keane conclusion from disjoint corridor routing in every box and the counting hypotheses
of
`burton_keane_uniqueness_full`. Those hypotheses are unsatisfiable for `d ≥ 1`, so the statement has
content only for `d = 0`. -/
lemma burton_keane_uniqueness_disjointRouting
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hroute : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))),
      ω ∈ threeMeetBox d n → DisjointCorridorRouting ω) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_corridorCover μ herg hfe bdry hbound hvol hdens
    (fun n => corridorCover_of_routing (fun ω hω => hroute n ω hω))

end DisjointPaths

end Percolation

end StatMech
