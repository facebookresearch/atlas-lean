/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierA.AllOpenCoarseProbabilityGeneral
import Code.FrontierA.MonotoneAutomatonCoarseTrifurcationGeneral
import Code.FrontierB.CurrentTraceClusterUniqueness
import Code.FrontierB.CurrentTraceCanonicalRouting

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierB

open Lattice ConfigSpace Percolation
open StatMech.FrontierA StatMech.Walls

variable {d : ℕ}





theorem removeSites_forceOpenFinset_eq_of_incident
    (T : Finset (Site d)) (F : Finset (Sym2 (Site d)))
    (hF : ∀ e ∈ F, ∃ t ∈ T, t ∈ e)
    (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites T (forceOpenFinset F ω) = removeSites T ω := by
  funext e
  unfold removeSites forceOpenFinset
  by_cases hinc : ∃ t ∈ T, t ∈ e
  · simp [hinc]
  · have heF : e ∉ F := by
      intro he
      exact hinc (hF e he)
    simp [hinc, heF]


theorem boxEdges_incident_to_box (d n : ℕ) :
    ∀ e ∈ boxEdges d n, ∃ t ∈ boxFinsetBK d n, t ∈ e := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hx : x ∈ box d n := (mem_boxEdges_iff.mp he).1
      exact ⟨x, mem_boxFinsetBK_iff.mpr hx, Sym2.mem_mk_left x y⟩



theorem removeBox_forceOpen_boxEdges_eq (d n : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites (bc61_boxAround d n 0) (forceOpenFinset (boxEdges d n) ω) =
      removeSites (bc61_boxAround d n 0) ω := by
  rw [bc61_boxAround_zero]
  exact removeSites_forceOpenFinset_eq_of_incident
    (boxFinsetBK d n) (boxEdges d n) (boxEdges_incident_to_box d n) ω



theorem forceOpen_boxEdges_bgfdIndexAllOpen
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    BgfdIndexAllOpen (forceOpenFinset (boxEdges d n) ω) n 0 := by
  intro x y hx hy hadj
  have hxbox : x ∈ box d n := by
    have h := bgfd_idx_iff_inBox.mp hx
    rw [bgfd_centre_zero] at h
    simpa [bgfdInBox] using h
  have hybox : y ∈ box d n := by
    have h := bgfd_idx_iff_inBox.mp hy
    rw [bgfd_centre_zero] at h
    simpa [bgfdInBox] using h
  exact forceOpenFinset_of_mem
    (mem_boxEdges_iff.mpr ⟨hxbox, hybox, hadj⟩) ω





theorem coarseTrif_forceOpen_boxEdges_of_coarse
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc61_IsCoarseTrifurcation ω n 0) :
    bc61_IsCoarseTrifurcation (forceOpenFinset (boxEdges d n) ω) n 0 := by
  obtain ⟨a₁, a₂, a₃, hi₁, hi₂, hi₃, hinf, hcut⟩ := h
  have hmono : ω ≤ forceOpenFinset (boxEdges d n) ω :=
    forceOpenFinset_le (boxEdges d n) ω
  refine ⟨a₁, a₂, a₃, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, hba⟩ := hi₁
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · obtain ⟨b, hb, hba⟩ := hi₂
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · obtain ⟨b, hb, hba⟩ := hi₃
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · simpa only [removeBox_forceOpen_boxEdges_eq] using hinf
  · simpa only [removeBox_forceOpen_boxEdges_eq] using hcut




theorem forceOpen_boxEdges_faithfulAllOpenTrif_of_threeMeetBox
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : ω ∈ threeMeetBox d n) :
    BgfdFaithfulAllOpenTrifAt
      (forceOpenFinset (boxEdges d n) ω) n 0 := by
  obtain ⟨_htop, x₁, x₂, x₃, hb₁, hb₂, hb₃,
    hi₁, hi₂, hi₃, hd₁₂, hd₁₃, hd₂₃⟩ := h
  have hb₁' : x₁ ∈ bc61_boxAround d n 0 := by
    rw [bc61_boxAround_zero]
    exact mem_boxFinsetBK_iff.mpr hb₁
  have hb₂' : x₂ ∈ bc61_boxAround d n 0 := by
    rw [bc61_boxAround_zero]
    exact mem_boxFinsetBK_iff.mpr hb₂
  have hb₃' : x₃ ∈ bc61_boxAround d n 0 := by
    rw [bc61_boxAround_zero]
    exact mem_boxFinsetBK_iff.mpr hb₃
  have hcoarse : bc61_IsCoarseTrifurcation ω n 0 :=
    coarseTrif_of_three_meetBox_general hi₁ hi₂ hi₃
      hd₁₂ hd₁₃ hd₂₃ hb₁' hb₂' hb₃'
  refine ⟨?_, forceOpen_boxEdges_bgfdIndexAllOpen ω n⟩
  rw [bgfd_centre_zero]
  exact (bc67_coarseTrif_is_G_n_trifurcation _ n 0).mp
    (coarseTrif_forceOpen_boxEdges_of_coarse ω n hcoarse)

theorem threeMeetBox_subset_force_faithfulAllOpenTrif (n : ℕ) :
    threeMeetBox d n ⊆
      (fun ω => forceOpenFinset (boxEdges d n) ω) ⁻¹'
        {ω | BgfdFaithfulAllOpenTrifAt ω n 0} := by
  intro ω hω
  exact forceOpen_boxEdges_faithfulAllOpenTrif_of_threeMeetBox ω n hω



theorem faithfulAllOpenTrif_pos_of_threeMeetBox
    (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hfe : HasLatticeFiniteEnergyMerge μ) (n : ℕ)
    (hpos : 0 < μ (threeMeetBox d n)) :
    0 < μ {ω | BgfdFaithfulAllOpenTrifAt ω n 0} :=
  pos_of_lattice_forceOpen_preimage μ hfe (boxEdges d n)
    (boxEdges_subset_hypercubic_edgeSet d n)
    (measurableSet_bgfdFaithfulAllOpenTrifAt n 0)
    (threeMeetBox_subset_force_faithfulAllOpenTrif n) hpos







theorem infiniteClusters_top_null_of_latticeFiniteEnergy
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasLatticeFiniteEnergyMerge μ) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  by_contra hne
  have htop : 0 < μ {ω | numInfiniteClusters d ω = ⊤} :=
    pos_iff_ne_zero.mpr hne
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos μ htop
  have hpos : 0 < μ {ω | BgfdFaithfulAllOpenTrifAt ω n 0} :=
    faithfulAllOpenTrif_pos_of_threeMeetBox μ hfe n hn
  exact (ne_of_gt hpos)
    (bgfdFaithfulAllOpenTrifAt_prob_eq_zero μ hd hinv n)



theorem latticeFiniteEnergy_coarse_uniqueness
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasLatticeFiniteEnergyMerge μ) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨
        μ {ω | numInfiniteClusters d ω = 1} = 1) ∧
      μ (atLeastTwoInfinite d) = 0 ∧
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  have htop := infiniteClusters_top_null_of_latticeFiniteEnergy
    μ hd herg.isTranslationInvariant hfe
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  have hktop : k ≠ ⊤ := by
    intro h
    subst k
    rw [hk] at htop
    exact one_ne_zero htop
  have hknot2 : ¬ 2 ≤ k := by
    intro hk2
    exact latticeInsertionMerge_excludes_finite_ge_two μ hfe hk hk2 hktop
  have hkle : k ≤ 1 := enat_le_one_of_not_two hknot2
  have hsub : {ω | numInfiniteClusters d ω = k} ⊆
      (atLeastTwoInfinite d)ᶜ := by
    intro ω hω
    rw [atLeastTwoInfinite_compl]
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω]
    exact hkle
  have hfull : μ (atLeastTwoInfinite d)ᶜ = 1 :=
    le_antisymm prob_le_one (hk ▸ measure_mono hsub)
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    (prob_compl_eq_one_iff measurableSet_atLeastTwoInfinite).mp hfull
  exact ⟨numInfiniteClusters_zero_or_one_of_const μ hk hmerge,
    hmerge, infiniteCluster_unique_ae μ herg hmerge⟩



theorem freeFreeSuperposedTraceLaw_coarse_uniqueness
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d))
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d))))) :
    let μ := (independentSuperposedTraceLaw
      (infiniteFreeCurrentMeasure d beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨
        μ {ω | numInfiniteClusters d ω = 1} = 1) ∧
      μ (atLeastTwoInfinite d) = 0 ∧
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  dsimp only
  exact latticeFiniteEnergy_coarse_uniqueness (d := d) _ hd herg
    (freeFreeSuperposedTraceLaw_hasLatticeFiniteEnergyMerge d beta hbeta)

theorem freePlusSuperposedTraceLaw_coarse_uniqueness
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d))
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d))))) :
    let μ := (independentSuperposedTraceLaw
      (infiniteFreeCurrentMeasure d beta hbeta.le)
      (infinitePlusCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨
        μ {ω | numInfiniteClusters d ω = 1} = 1) ∧
      μ (atLeastTwoInfinite d) = 0 ∧
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  dsimp only
  exact latticeFiniteEnergy_coarse_uniqueness (d := d) _ hd herg
    (freePlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge d beta hbeta)

theorem plusPlusSuperposedTraceLaw_coarse_uniqueness
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d))
      (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d))))) :
    let μ := (independentSuperposedTraceLaw
      (infinitePlusCurrentMeasure d beta hbeta.le)
      (infinitePlusCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨
        μ {ω | numInfiniteClusters d ω = 1} = 1) ∧
      μ (atLeastTwoInfinite d) = 0 ∧
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  dsimp only
  exact latticeFiniteEnergy_coarse_uniqueness (d := d) _ hd herg
    (plusPlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge d beta hbeta)

end StatMech.FrontierB
