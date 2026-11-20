/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierB.CurrentTraceClusterUniqueness
import Code.Percolation.HrouteDisjointPaths
import Code.Percolation.MengerRouting
import Code.Percolation.TrifurcationExistence

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierB

open Lattice ConfigSpace Percolation
open Percolation.DisjointPaths

variable {d : ℕ}



theorem latticeEdgePart_subset_edgeSet (G : Finset (Sym2 (Site d))) :
    (↑(latticeEdgePart d G) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
  latticeEdgePart_lattice d G

theorem forceOpenFinset_latticeEdgePart_apply
    (G : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    {e : Sym2 (Site d)} (he : e ∈ (hypercubicLattice d).edgeSet) :
    forceOpenFinset (latticeEdgePart d G) ω e = forceOpenFinset G ω e := by
  simp [forceOpenFinset, latticeEdgePart, he]




theorem corridorStep_latticeEdgePart_iff
    (G : Finset (Sym2 (Site d))) (x y : Site d) :
    CorridorStep (latticeEdgePart d G) x y ↔ CorridorStep G x y := by
  constructor
  · rintro ⟨hadj, hmem, hzero⟩
    exact ⟨hadj, latticeEdgePart_subset d G hmem, hzero⟩
  · rintro ⟨hadj, hmem, hzero⟩
    refine ⟨hadj, ?_, hzero⟩
    change s(x, y) ∈ G.filter
      (fun e => e ∈ (hypercubicLattice d).edgeSet)
    rw [Finset.mem_filter]
    refine ⟨hmem, ?_⟩
    rw [SimpleGraph.mem_edgeSet]
    exact hadj



theorem corridor_latticeEdgePart_iff
    (G : Finset (Sym2 (Site d))) (x y : Site d) :
    Relation.ReflTransGen (CorridorStep (latticeEdgePart d G)) x y ↔
      Relation.ReflTransGen (CorridorStep G) x y := by
  constructor
  · exact Relation.ReflTransGen.mono fun _ _ h =>
      (corridorStep_latticeEdgePart_iff G _ _).mp h
  · exact Relation.ReflTransGen.mono fun _ _ h =>
      (corridorStep_latticeEdgePart_iff G _ _).mpr h



theorem openSubgraph_forceOpenFinset_latticeEdgePart
    (G : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (forceOpenFinset (latticeEdgePart d G) ω) =
      openSubgraph d (forceOpenFinset G ω) := by
  ext x y
  simp only [openSubgraph_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    have hedge : s(x, y) ∈ (hypercubicLattice d).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hadj
    exact ⟨hadj, by
      rwa [forceOpenFinset_latticeEdgePart_apply G ω hedge] at hopen⟩
  · rintro ⟨hadj, hopen⟩
    have hedge : s(x, y) ∈ (hypercubicLattice d).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hadj
    exact ⟨hadj, by
      rwa [forceOpenFinset_latticeEdgePart_apply G ω hedge]⟩

theorem removeSite_forceOpenFinset_latticeEdgePart_apply
    (z : Site d) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) {e : Sym2 (Site d)}
    (he : e ∈ (hypercubicLattice d).edgeSet) :
    removeSite z (forceOpenFinset (latticeEdgePart d G) ω) e =
      removeSite z (forceOpenFinset G ω) e := by
  unfold removeSite
  by_cases hz : z ∈ e
  · simp [hz]
  · simp only [hz, if_false]
    exact forceOpenFinset_latticeEdgePart_apply G ω he



theorem openSubgraph_removeSite_forceOpenFinset_latticeEdgePart
    (z : Site d) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d
        (removeSite z (forceOpenFinset (latticeEdgePart d G) ω)) =
      openSubgraph d (removeSite z (forceOpenFinset G ω)) := by
  ext x y
  simp only [openSubgraph_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    have hedge : s(x, y) ∈ (hypercubicLattice d).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hadj
    exact ⟨hadj, by
      rwa [removeSite_forceOpenFinset_latticeEdgePart_apply z G ω hedge] at hopen⟩
  · rintro ⟨hadj, hopen⟩
    have hedge : s(x, y) ∈ (hypercubicLattice d).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hadj
    exact ⟨hadj, by
      rwa [removeSite_forceOpenFinset_latticeEdgePart_apply z G ω hedge]⟩

theorem cluster_removeSite_forceOpenFinset_latticeEdgePart
    (z x : Site d) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    cluster d (removeSite z (forceOpenFinset (latticeEdgePart d G) ω)) x =
      cluster d (removeSite z (forceOpenFinset G ω)) x := by
  ext y
  simp only [mem_cluster]
  change
    (openSubgraph d
      (removeSite z (forceOpenFinset (latticeEdgePart d G) ω))).Reachable x y ↔
    (openSubgraph d (removeSite z (forceOpenFinset G ω))).Reachable x y
  rw [openSubgraph_removeSite_forceOpenFinset_latticeEdgePart]



theorem corridorWorks_latticeEdgePart
    (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) :
    CorridorWorks a₁ a₂ a₃ (latticeEdgePart d G) =
      CorridorWorks a₁ a₂ a₃ G := by
  ext ω
  simp only [CorridorWorks, Set.mem_setOf_eq]
  rw [cluster_removeSite_forceOpenFinset_latticeEdgePart,
    cluster_removeSite_forceOpenFinset_latticeEdgePart,
    cluster_removeSite_forceOpenFinset_latticeEdgePart]





def OriginNeighborsCutConnected
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∀ a b : Site d, (hypercubicLattice d).Adj 0 a →
    (hypercubicLattice d).Adj 0 b → Connected d (removeSite 0 ω) a b





theorem not_mengerCore_of_originNeighborsCutConnected
    (ω : ConfigSpace (Sym2 (Site d)))
    (hconn : OriginNeighborsCutConnected ω) :
    ¬ MengerCore ω := by
  rintro ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, _hne, hadj,
    ⟨hcor₁, hcor₂, _hcor₃⟩, _hinf, ⟨hd12, _hd13, _hd23⟩⟩
  let ϱ := removeSite (0 : Site d) (forceOpenFinset G ω)
  have hle : removeSite (0 : Site d) ω ≤ ϱ := by
    intro e
    by_cases hzero : (0 : Site d) ∈ e
    · simp [ϱ, removeSite, hzero]
    · simp only [ϱ, removeSite, hzero, if_false]
      exact forceOpenFinset_le G ω e
  have ha12 : Connected d ϱ a₁ a₂ :=
    connected_mono hle (hconn a₁ a₂ hadj.1 hadj.2.1)
  have haw₁ : Connected d ϱ a₁ w₁ :=
    connected_removeSite_forceOpen_of_corridor ω G hcor₁
  have haw₂ : Connected d ϱ a₂ w₂ :=
    connected_removeSite_forceOpen_of_corridor ω G hcor₂
  have hw12 : Connected d ϱ w₁ w₂ := haw₁.symm.trans (ha12.trans haw₂)
  exact hd12 (cluster_eq_of_connected hw12)






def HubCorridorWorks (z a₁ a₂ a₃ : Site d)
    (G : Finset (Sym2 (Site d))) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj z a₁ ∧
      (hypercubicLattice d).Adj z a₂ ∧
      (hypercubicLattice d).Adj z a₃) ∧
    ((cluster d (removeSite z (forceOpenFinset G ω)) a₁).Infinite ∧
      (cluster d (removeSite z (forceOpenFinset G ω)) a₂).Infinite ∧
      (cluster d (removeSite z (forceOpenFinset G ω)) a₃).Infinite) ∧
    (cluster d (removeSite z (forceOpenFinset G ω)) a₁ ≠
        cluster d (removeSite z (forceOpenFinset G ω)) a₂ ∧
      cluster d (removeSite z (forceOpenFinset G ω)) a₁ ≠
        cluster d (removeSite z (forceOpenFinset G ω)) a₃ ∧
      cluster d (removeSite z (forceOpenFinset G ω)) a₂ ≠
        cluster d (removeSite z (forceOpenFinset G ω)) a₃)}


theorem hubCorridorWorks_latticeEdgePart
    (z a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) :
    HubCorridorWorks z a₁ a₂ a₃ (latticeEdgePart d G) =
      HubCorridorWorks z a₁ a₂ a₃ G := by
  ext ω
  simp only [HubCorridorWorks, Set.mem_setOf_eq]
  rw [cluster_removeSite_forceOpenFinset_latticeEdgePart,
    cluster_removeSite_forceOpenFinset_latticeEdgePart,
    cluster_removeSite_forceOpenFinset_latticeEdgePart]


def hubTripleEdges (z a₁ a₂ a₃ : Site d) :
    Finset (Sym2 (Site d)) :=
  {s(z, a₁), s(z, a₂), s(z, a₃)}



theorem hubTripleEdges_subset_edgeSet (z a₁ a₂ a₃ : Site d)
    (hadj : (hypercubicLattice d).Adj z a₁ ∧
      (hypercubicLattice d).Adj z a₂ ∧
      (hypercubicLattice d).Adj z a₃) :
    (↑(hubTripleEdges z a₁ a₂ a₃) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
  intro e he
  change e ∈ ({s(z, a₁), s(z, a₂), s(z, a₃)} :
    Finset (Sym2 (Site d))) at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · rw [SimpleGraph.mem_edgeSet]
    exact hadj.1
  · rw [SimpleGraph.mem_edgeSet]
    exact hadj.2.1
  · rw [SimpleGraph.mem_edgeSet]
    exact hadj.2.2



theorem hubCombinedEdges_subset_edgeSet (z a₁ a₂ a₃ : Site d)
    (G : Finset (Sym2 (Site d)))
    (hadj : (hypercubicLattice d).Adj z a₁ ∧
      (hypercubicLattice d).Adj z a₂ ∧
      (hypercubicLattice d).Adj z a₃) :
    (↑(hubTripleEdges z a₁ a₂ a₃ ∪ latticeEdgePart d G) :
      Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet := by
  intro e he
  change e ∈ hubTripleEdges z a₁ a₂ a₃ ∪ latticeEdgePart d G at he
  rw [Finset.mem_union] at he
  rcases he with hstar | hroute
  · exact hubTripleEdges_subset_edgeSet z a₁ a₂ a₃ hadj hstar
  · exact latticeEdgePart_subset_edgeSet G hroute





theorem isCanonicalTrifurcation_of_neighbors_at
    (ω : ConfigSpace (Sym2 (Site d))) (z a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj z a₁ ∧
      (hypercubicLattice d).Adj z a₂ ∧
      (hypercubicLattice d).Adj z a₃)
    (hinf : (cluster d (removeSite z ω) a₁).Infinite ∧
      (cluster d (removeSite z ω) a₂).Infinite ∧
      (cluster d (removeSite z ω) a₃).Infinite)
    (hsep : ¬ Connected d (removeSite z ω) a₁ a₂ ∧
      ¬ Connected d (removeSite z ω) a₁ a₃ ∧
      ¬ Connected d (removeSite z ω) a₂ a₃) :
    IsCanonicalTrifurcation d
      (forceOpenFinset (hubTripleEdges z a₁ a₂ a₃) ω) z := by
  classical
  let F := hubTripleEdges z a₁ a₂ a₃
  change IsCanonicalTrifurcation d (forceOpenFinset F ω) z
  have hF : ∀ e ∈ F, z ∈ e := by
    intro e he
    simp only [F, hubTripleEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> exact Sym2.mem_mk_left _ _
  have hrm : removeSite z (forceOpenFinset F ω) = removeSite z ω :=
    removeSite_forceOpen_eq z F hF ω
  refine ⟨a₁, a₂, a₃, hne, ?_, ?_, ?_⟩
  · exact ⟨⟨hadj.1, forceOpenFinset_of_mem (by simp [F, hubTripleEdges]) ω⟩,
      ⟨hadj.2.1, forceOpenFinset_of_mem (by simp [F, hubTripleEdges]) ω⟩,
      ⟨hadj.2.2, forceOpenFinset_of_mem (by simp [F, hubTripleEdges]) ω⟩⟩
  · rwa [hrm]
  · rwa [hrm]



theorem hubCorridorWorks_subset_force_canonical
    (z a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) :
    HubCorridorWorks z a₁ a₂ a₃ G ⊆
      (fun ω => forceOpenFinset
        (hubTripleEdges z a₁ a₂ a₃ ∪ G) ω) ⁻¹'
        {ω | IsCanonicalTrifurcation d ω z} := by
  rintro ω ⟨hne, hadj, hinf, hdiff⟩
  change IsCanonicalTrifurcation d
    (forceOpenFinset (hubTripleEdges z a₁ a₂ a₃ ∪ G) ω) z
  rw [← tre_forceOpenFinset_comp]
  refine isCanonicalTrifurcation_of_neighbors_at
    (forceOpenFinset G ω) z a₁ a₂ a₃ hne hadj hinf ?_
  refine ⟨?_, ?_, ?_⟩
  · intro hconn
    exact hdiff.1 (cluster_eq_of_connected hconn)
  · intro hconn
    exact hdiff.2.1 (cluster_eq_of_connected hconn)
  · intro hconn
    exact hdiff.2.2 (cluster_eq_of_connected hconn)



theorem pos_of_lattice_forceOpen_preimage
    (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hfe : HasLatticeFiniteEnergyMerge μ)
    (F : Finset (Sym2 (Site d)))
    (hFL : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {A B : Set (ConfigSpace (Sym2 (Site d)))}
    (hmB : MeasurableSet B)
    (hsub : A ⊆ (fun ω => forceOpenFinset F ω) ⁻¹' B)
    (hApos : 0 < μ A) : 0 < μ B := by
  by_contra hnot
  rw [not_lt, nonpos_iff_eq_zero] at hnot
  have hac : μ.map (fun ω => forceOpenFinset F ω) ≪ μ := hfe F hFL
  have hpush : (μ.map (fun ω => forceOpenFinset F ω)) B =
      μ ((fun ω => forceOpenFinset F ω) ⁻¹' B) :=
    Measure.map_apply (measurable_forceOpenFinset F) hmB
  have hpre0 : μ ((fun ω => forceOpenFinset F ω) ⁻¹' B) = 0 := by
    rw [← hpush]
    exact hac hnot
  have hle : μ A ≤ μ ((fun ω => forceOpenFinset F ω) ⁻¹' B) :=
    measure_mono hsub
  rw [hpre0] at hle
  exact (ne_of_gt hApos) (le_antisymm hle bot_le)





theorem canonicalTrifurcation_pos_of_variableHubCorridorCover
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasLatticeFiniteEnergyMerge μ) {n : ℕ}
    (hcover : threeMeetBox d n ⊆
      ⋃ (z : Site d) (a₁ : Site d) (a₂ : Site d) (a₃ : Site d)
          (G : Finset (Sym2 (Site d))),
        HubCorridorWorks z a₁ a₂ a₃ G)
    (hpos : 0 < μ (threeMeetBox d n)) :
    0 < μ {ω | IsCanonicalTrifurcation d ω 0} := by
  classical
  let ι := Site d × Site d × Site d × Site d ×
    Finset (Sym2 (Site d))
  let B : ι → Set (ConfigSpace (Sym2 (Site d))) := fun p =>
    HubCorridorWorks p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  have hcover' : threeMeetBox d n ⊆ ⋃ p : ι, B p := by
    intro ω hω
    obtain ⟨z, a₁, a₂, a₃, G, hworks⟩ := by
      simpa only [Set.mem_iUnion] using hcover hω
    exact Set.mem_iUnion.mpr ⟨(z, a₁, a₂, a₃, G), hworks⟩
  obtain ⟨p, hppos⟩ := exists_pos_of_cover μ hcover' hpos
  obtain ⟨z, a₁, a₂, a₃, G⟩ := p
  have hnorm : 0 < μ
      (HubCorridorWorks z a₁ a₂ a₃ (latticeEdgePart d G)) := by
    rwa [hubCorridorWorks_latticeEdgePart]
  obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero (ne_of_gt hnorm)
  have hlegal :
      (↑(hubTripleEdges z a₁ a₂ a₃ ∪ latticeEdgePart d G) :
        Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet :=
    hubCombinedEdges_subset_edgeSet z a₁ a₂ a₃ G hω.2.1
  have hz : 0 < μ {ω | IsCanonicalTrifurcation d ω z} :=
    pos_of_lattice_forceOpen_preimage μ hfe
      (hubTripleEdges z a₁ a₂ a₃ ∪ latticeEdgePart d G) hlegal
      (ctp_measurableSet_isCanonicalTrifurcation z)
      (hubCorridorWorks_subset_force_canonical z a₁ a₂ a₃
        (latticeEdgePart d G)) hnorm
  rwa [ctp_canonicalTrifurcationProb_const μ hinv z] at hz



theorem canonicalTrifurcation_pos_of_variableHubCorridorCovers
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasLatticeFiniteEnergyMerge μ)
    (hcover : ∀ n : ℕ, threeMeetBox d n ⊆
      ⋃ (z : Site d) (a₁ : Site d) (a₂ : Site d) (a₃ : Site d)
          (G : Finset (Sym2 (Site d))),
        HubCorridorWorks z a₁ a₂ a₃ G)
    (htop : 0 < μ {ω | numInfiniteClusters d ω = ⊤}) :
    0 < μ {ω | IsCanonicalTrifurcation d ω 0} := by
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos μ htop
  exact canonicalTrifurcation_pos_of_variableHubCorridorCover
    μ hinv hfe (hcover n) hn



theorem originTripleEdges_subset_edgeSet (a₁ a₂ a₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧
      (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) :
    (↑({s((0 : Site d), a₁), s((0 : Site d), a₂),
        s((0 : Site d), a₃)} : Finset (Sym2 (Site d))) :
      Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet := by
  simpa only [hubTripleEdges] using
    hubTripleEdges_subset_edgeSet (0 : Site d) a₁ a₂ a₃ hadj



theorem isCanonicalTrifurcation_of_neighbors
    (ω : ConfigSpace (Sym2 (Site d))) (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧
      (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite)
    (hsep : ¬ Connected d (removeSite 0 ω) a₁ a₂ ∧
      ¬ Connected d (removeSite 0 ω) a₁ a₃ ∧
      ¬ Connected d (removeSite 0 ω) a₂ a₃) :
    IsCanonicalTrifurcation d
      (forceOpenFinset {s((0 : Site d), a₁), s((0 : Site d), a₂),
        s((0 : Site d), a₃)} ω) 0 := by
  simpa only [hubTripleEdges] using
    isCanonicalTrifurcation_of_neighbors_at
      ω (0 : Site d) a₁ a₂ a₃ hne hadj hinf hsep

theorem precursor_subset_force_canonical (a₁ a₂ a₃ : Site d) :
    NeighborTrifPrecursor d a₁ a₂ a₃ ⊆
      (fun ω => forceOpenFinset
        {s((0 : Site d), a₁), s((0 : Site d), a₂),
          s((0 : Site d), a₃)} ω) ⁻¹'
        {ω | IsCanonicalTrifurcation d ω 0} := by
  rintro ω ⟨hne, hadj, hinf, hsep⟩
  exact isCanonicalTrifurcation_of_neighbors ω a₁ a₂ a₃ hne hadj hinf hsep



theorem canonicalTrifurcation_pos_of_precursor_lattice
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasLatticeFiniteEnergyMerge μ) (a₁ a₂ a₃ : Site d)
    (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ {ω | IsCanonicalTrifurcation d ω 0} := by
  classical
  obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero (ne_of_gt hpos)
  let F : Finset (Sym2 (Site d)) :=
    {s((0 : Site d), a₁), s((0 : Site d), a₂), s((0 : Site d), a₃)}
  have hFL : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
    originTripleEdges_subset_edgeSet a₁ a₂ a₃ hω.2.1
  by_contra h
  rw [not_lt, nonpos_iff_eq_zero] at h
  have hac : μ.map (fun ω => forceOpenFinset F ω) ≪ μ := hfe F hFL
  have hpush : (μ.map (fun ω => forceOpenFinset F ω))
      {ω | IsCanonicalTrifurcation d ω 0} =
      μ ((fun ω => forceOpenFinset F ω) ⁻¹'
        {ω | IsCanonicalTrifurcation d ω 0}) :=
    Measure.map_apply (measurable_forceOpenFinset F)
      (ctp_measurableSet_isCanonicalTrifurcation 0)
  have hpre0 : μ ((fun ω => forceOpenFinset F ω) ⁻¹'
      {ω | IsCanonicalTrifurcation d ω 0}) = 0 := by
    rw [← hpush]
    exact hac h
  have hle : μ (NeighborTrifPrecursor d a₁ a₂ a₃) ≤
      μ ((fun ω => forceOpenFinset F ω) ⁻¹'
        {ω | IsCanonicalTrifurcation d ω 0}) :=
    measure_mono (precursor_subset_force_canonical a₁ a₂ a₃)
  rw [hpre0] at hle
  exact (ne_of_gt hpos) (le_antisymm hle bot_le)

end StatMech.FrontierB
