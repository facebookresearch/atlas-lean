/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Percolation.BKUniqueness2

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}











noncomputable def forceOpenFinset (F : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) : ConfigSpace (Sym2 (Site d)) :=
  fun e => if e ∈ F then true else ω e

@[simp] lemma forceOpenFinset_of_mem {F : Finset (Sym2 (Site d))} {e : Sym2 (Site d)}
    (h : e ∈ F) (ω : ConfigSpace (Sym2 (Site d))) : forceOpenFinset F ω e = true := by
  simp [forceOpenFinset, h]

@[simp] lemma forceOpenFinset_of_notMem {F : Finset (Sym2 (Site d))} {e : Sym2 (Site d)}
    (h : e ∉ F) (ω : ConfigSpace (Sym2 (Site d))) : forceOpenFinset F ω e = ω e := by
  simp [forceOpenFinset, h]


lemma forceOpenFinset_le (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) :
    ω ≤ forceOpenFinset F ω := by
  intro e; unfold forceOpenFinset; by_cases h : e ∈ F <;> simp [h]


theorem measurable_forceOpenFinset (F : Finset (Sym2 (Site d))) :
    Measurable (fun ω : ConfigSpace (Sym2 (Site d)) => forceOpenFinset F ω) := by
  apply measurable_pi_lambda
  intro e
  unfold forceOpenFinset
  by_cases h : e ∈ F
  · simp [h]
  · simp only [h, if_false]; exact measurable_pi_apply e







lemma openSubgraph_mono {ω ω' : ConfigSpace (Sym2 (Site d))} (hle : ω ≤ ω') :
    openSubgraph d ω ≤ openSubgraph d ω' := by
  intro x y h
  rw [openSubgraph_adj] at h ⊢
  refine ⟨h.1, ?_⟩
  have := hle s(x, y); rw [h.2] at this; exact le_antisymm (by simp) this


lemma connected_mono {ω ω' : ConfigSpace (Sym2 (Site d))} (hle : ω ≤ ω')
    {x y : Site d} (h : Connected d ω x y) : Connected d ω' x y :=
  h.mono (openSubgraph_mono hle)


lemma cluster_mono {ω ω' : ConfigSpace (Sym2 (Site d))} (hle : ω ≤ ω') (x : Site d) :
    cluster d ω x ⊆ cluster d ω' x := fun _ hy => connected_mono hle hy







theorem encard_image_lt_of_not_injOn {α β : Type*} {s : Set α} {f : α → β}
    (hfin : s.Finite) (hni : ¬ Set.InjOn f s) :
    (f '' s).encard < s.encard := by
  rcases lt_or_eq_of_le (Set.encard_image_le f s) with h | h
  · exact h
  · exact absurd (hfin.injOn_of_encard_image_eq h) hni









def anchorSites (F : Finset (Sym2 (Site d))) : Set (Site d) :=
  {a | ∃ e ∈ F, a ∈ e}


lemma anchorSites_finite (F : Finset (Sym2 (Site d))) : (anchorSites F).Finite := by
  have hsub : anchorSites F ⊆ ⋃ e ∈ F, {a | a ∈ e} := by
    intro a ha; obtain ⟨e, he, hae⟩ := ha; exact Set.mem_biUnion he hae
  apply Set.Finite.subset _ hsub
  apply Set.Finite.biUnion F.finite_toSet
  intro e _
  induction e with
  | h p q =>
    have h2 : {a : Site d | a ∈ s(p, q)} ⊆ ({p, q} : Set (Site d)) := by
      intro a ha
      simp only [Set.mem_setOf_eq, Sym2.mem_iff] at ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact ha
    exact Set.Finite.subset ((Set.finite_singleton q).insert p) h2



lemma adj_forceOpenFinset_cases (F : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (h : (openSubgraph d (forceOpenFinset F ω)).Adj x y) :
    (openSubgraph d ω).Adj x y ∨ (s(x, y) ∈ F) := by
  rw [openSubgraph_adj] at h
  by_cases hF : s(x, y) ∈ F
  · exact Or.inr hF
  · left
    rw [openSubgraph_adj]
    exact ⟨h.1, by rw [← forceOpenFinset_of_notMem hF ω]; exact h.2⟩



lemma anchor_decomp (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (x z : Site d) (h : Connected d (forceOpenFinset F ω) x z) :
    Connected d ω x z ∨ ∃ a ∈ anchorSites F, Connected d ω a z := by
  unfold Connected at h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl connected_rfl
  | @tail b c hxb hbc ih =>
    rcases adj_forceOpenFinset_cases F ω hbc with hadj | hF
    · rcases ih with hxb' | ⟨a, ha, hab⟩
      · exact Or.inl (hxb'.trans (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj))
      · exact Or.inr ⟨a, ha, hab.trans (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj)⟩
    · exact Or.inr ⟨c, ⟨s(b, c), hF, Sym2.mem_mk_right b c⟩, connected_rfl⟩














lemma exists_infinite_omega_cluster_in_D (F : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hD : (cluster d (forceOpenFinset F ω) x).Infinite) :
    ∃ a, a ∈ cluster d (forceOpenFinset F ω) x ∧ (cluster d ω a).Infinite := by
  set ω' := forceOpenFinset F ω with hω'
  set D := cluster d ω' x with hDdef
  set S : Set (Site d) := insert x (anchorSites F) with hS
  have hSfin : S.Finite := (anchorSites_finite F).insert x
  
  have hcover : D ⊆ ⋃ a ∈ S, cluster d ω a := by
    intro z hz
    rw [hDdef, mem_cluster] at hz
    rcases anchor_decomp F ω x z hz with hconn | ⟨a, ha, haz⟩
    · exact Set.mem_biUnion (Set.mem_insert x _) (by rw [mem_cluster]; exact hconn)
    · exact Set.mem_biUnion (Set.mem_insert_of_mem x ha) (by rw [mem_cluster]; exact haz)
  have hcover2 : D ⊆ ⋃ a ∈ S, (cluster d ω a ∩ D) := by
    intro z hz
    obtain ⟨T, hT, hzT⟩ := Set.mem_iUnion₂.mp (hcover hz)
    exact Set.mem_iUnion₂.mpr ⟨T, hT, hzT, hz⟩
  
  have hpiece : ∃ a ∈ S, (cluster d ω a ∩ D).Infinite := by
    by_contra hcon
    simp only [not_exists, not_and, Set.not_infinite] at hcon
    exact hD ((hSfin.biUnion hcon).subset hcover2)
  obtain ⟨a, _, hainf⟩ := hpiece
  obtain ⟨w, hwa, hwD⟩ := hainf.nonempty
  refine ⟨w, hwD, ?_⟩
  have hca : (cluster d ω a).Infinite := hainf.mono Set.inter_subset_left
  rw [mem_cluster] at hwa
  rw [← cluster_eq_of_connected hwa]
  exact hca













theorem forceOpen_image_repSet_eq (F : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    (fun a => cluster d (forceOpenFinset F ω) a) '' (repSet d ω)
      = infiniteClusters d (forceOpenFinset F ω) := by
  set ω' := forceOpenFinset F ω with hω'
  have hle : ω ≤ ω' := forceOpenFinset_le F ω
  ext D
  simp only [Set.mem_image, infiniteClusters, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha.1.mono (cluster_mono hle a), a, rfl⟩
  · rintro ⟨hinf, x, rfl⟩
    obtain ⟨w, hwD, hwinf⟩ := exists_infinite_omega_cluster_in_D F ω x hinf
    obtain ⟨r, hr, hmin⟩ := exists_encode_min (cluster d ω w) ⟨w, self_mem_cluster ω w⟩
    rw [mem_cluster] at hr
    refine ⟨r, ⟨?_, ?_⟩, ?_⟩
    · rw [← cluster_eq_of_connected hr]; exact hwinf
    · intro y hry; exact hmin y (by rw [mem_cluster]; exact hr.trans hry)
    · have hrw' : Connected d ω' r w := connected_mono hle hr.symm
      rw [mem_cluster] at hwD
      exact cluster_eq_of_connected (hrw'.trans hwD.symm)











theorem numInfiniteClusters_lt_of_merge
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hfin : numInfiniteClusters d ω ≠ ⊤)
    (x y : Site d) (hx : (cluster d ω x).Infinite) (hy : (cluster d ω y).Infinite)
    (hne : cluster d ω x ≠ cluster d ω y)
    (hmerge : Connected d (forceOpenFinset F ω) x y) :
    numInfiniteClusters d (forceOpenFinset F ω) < numInfiniteClusters d ω := by
  set ω' := forceOpenFinset F ω with hω'
  have hle : ω ≤ ω' := forceOpenFinset_le F ω
  
  have hrepfin : (repSet d ω).Finite := by
    rw [← Set.not_infinite]
    intro hinf
    exact hfin (by rw [numInfiniteClusters_eq_repSet_encard]; exact hinf.encard_eq)
  
  obtain ⟨rx, hrx, hminx⟩ := exists_encode_min (cluster d ω x) ⟨x, self_mem_cluster ω x⟩
  obtain ⟨ry, hry, hminy⟩ := exists_encode_min (cluster d ω y) ⟨y, self_mem_cluster ω y⟩
  rw [mem_cluster] at hrx hry
  have hrxrep : rx ∈ repSet d ω :=
    ⟨by rw [← cluster_eq_of_connected hrx]; exact hx,
     fun z hz => hminx z (by rw [mem_cluster]; exact hrx.trans hz)⟩
  have hryrep : ry ∈ repSet d ω :=
    ⟨by rw [← cluster_eq_of_connected hry]; exact hy,
     fun z hz => hminy z (by rw [mem_cluster]; exact hry.trans hz)⟩
  
  have hrxry : rx ≠ ry := by
    intro h
    exact hne (by rw [cluster_eq_of_connected hrx, cluster_eq_of_connected hry, h])
  
  have hpsieq : cluster d ω' rx = cluster d ω' ry := by
    have h1 : Connected d ω' rx x := connected_mono hle hrx.symm
    have h2 : Connected d ω' y ry := connected_mono hle hry
    exact cluster_eq_of_connected ((h1.trans hmerge).trans h2)
  
  have hni : ¬ Set.InjOn (fun a => cluster d ω' a) (repSet d ω) := fun hinj =>
    hrxry (hinj hrxrep hryrep hpsieq)
  
  have hlhs : numInfiniteClusters d ω'
      = ((fun a => cluster d ω' a) '' (repSet d ω)).encard := by
    rw [hω', forceOpen_image_repSet_eq F ω]; rfl
  rw [hlhs, numInfiniteClusters_eq_repSet_encard ω]
  exact encard_image_lt_of_not_injOn hrepfin hni










def MergeWitness (d : ℕ) (F : Finset (Sym2 (Site d))) (k : ℕ∞) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | numInfiniteClusters d ω = k ∧
    ∃ x y : Site d, (cluster d ω x).Infinite ∧ (cluster d ω y).Infinite ∧
      cluster d ω x ≠ cluster d ω y ∧ Connected d (forceOpenFinset F ω) x y}



theorem mergeWitness_subset_force_lt (F : Finset (Sym2 (Site d))) {k : ℕ∞} (hk : k ≠ ⊤) :
    MergeWitness d F k ⊆
      (fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k} := by
  intro ω hω
  obtain ⟨hkeq, x, y, hx, hy, hne, hmerge⟩ := hω
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hfin : numInfiniteClusters d ω ≠ ⊤ := by rw [hkeq]; exact hk
  have := numInfiniteClusters_lt_of_merge F ω hfin x y hx hy hne hmerge
  rwa [hkeq] at this









theorem measurableSet_numInfiniteClusters_lt (k : ℕ∞) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω < k} :=
  measurable_numInfiniteClusters (MeasurableSet.of_discrete)


theorem numInfiniteClusters_lt_null
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    μ {ω | numInfiniteClusters d ω < k} = 0 := by
  have hdisj : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω < k}ᶜ := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hω]; exact lt_irrefl k
  have hfull : μ {ω | numInfiniteClusters d ω < k}ᶜ = 1 :=
    le_antisymm prob_le_one (hk ▸ measure_mono hdisj)
  exact (prob_compl_eq_one_iff (measurableSet_numInfiniteClusters_lt k)).mp hfull







def HasFiniteEnergyMerge (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ F : Finset (Sym2 (Site d)), (μ.map (fun ω => forceOpenFinset F ω)) ≪ μ






theorem merge_contradiction
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
    (F : Finset (Sym2 (Site d)))
    (hfe : (μ.map (fun ω => forceOpenFinset F ω)) ≪ μ)
    {A : Set (ConfigSpace (Sym2 (Site d)))}
    (hApos : 0 < μ A)
    (hAsub : A ⊆ (fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k}) :
    False := by
  have hnullset := numInfiniteClusters_lt_null μ hk
  have hpush : (μ.map (fun ω => forceOpenFinset F ω)) {ω | numInfiniteClusters d ω < k}
      = μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k}) :=
    Measure.map_apply (measurable_forceOpenFinset F) (measurableSet_numInfiniteClusters_lt k)
  have hpre0 :
      μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k}) = 0 := by
    rw [← hpush]; exact hfe hnullset
  have hAle :
      μ A ≤ μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k}) :=
    measure_mono hAsub
  rw [hpre0] at hAle
  exact absurd (le_antisymm hAle bot_le) (ne_of_gt hApos)
























theorem burton_keane_merge_excludes_finite_ge_two
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → 2 ≤ k → k = ⊤ := by
  intro k hk hk2
  by_contra hktop
  obtain ⟨F, hFpos⟩ := hmergeGeom k hk2 hktop hk
  exact merge_contradiction μ hk F (hfe F) hFpos (mergeWitness_subset_force_lt F hktop)










theorem merge_event_null
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    μ (atLeastTwoInfinite d) = 0 := by
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  have hktop : k ≠ ⊤ := hkne_top k hk
  
  have hknot2 : ¬ (2 ≤ k) := by
    intro h2
    exact hktop (burton_keane_merge_excludes_finite_ge_two μ hfe hmergeGeom k hk h2)
  
  have hkle : k ≤ 1 := enat_le_one_of_not_two hknot2
  have hsub : {ω | numInfiniteClusters d ω = k} ⊆ (atLeastTwoInfinite d)ᶜ := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rw [atLeastTwoInfinite_compl]
    simp only [Set.mem_setOf_eq, hω]; exact hkle
  have hfull : μ (atLeastTwoInfinite d)ᶜ = 1 := le_antisymm prob_le_one (hk ▸ measure_mono hsub)
  exact (prob_compl_eq_one_iff measurableSet_atLeastTwoInfinite).mp hfull




























theorem burton_keane_uniqueness_via_merge
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0})
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
    intro k hk
    obtain ⟨k', hk'top, hk'⟩ :=
      numInfiniteClusters_ae_const_ne_top μ herg bdry hbound hvol hdens htrif
    
    intro hktop
    have hsub : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω = k'}ᶜ := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hω]
      intro h; exact hk'top (by rw [← h, hktop])
    have hmk' : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'} := by
      have heq : {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'}
          = numInfiniteClusters d ⁻¹' {k'} := by ext ω; simp [Set.mem_preimage]
      rw [heq]; exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)
    have hfull : μ {ω | numInfiniteClusters d ω = k'}ᶜ = 1 :=
      le_antisymm prob_le_one (hk ▸ measure_mono hsub)
    have hnull : μ {ω | numInfiniteClusters d ω = k'} = 0 :=
      (prob_compl_eq_one_iff hmk').mp hfull
    rw [hk'] at hnull
    exact one_ne_zero hnull
  
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top hmergeGeom
  
  refine ⟨numInfiniteClusters_zero_or_one μ herg hmerge, hmerge,
    infiniteCluster_unique_ae μ herg hmerge⟩

end Percolation

end StatMech
