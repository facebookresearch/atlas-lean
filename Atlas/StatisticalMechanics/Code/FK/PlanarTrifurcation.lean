/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.InfiniteFiniteEnergy
import Code.Walls.binsclosure
import Code.Percolation.CanonTrifProb
import Code.Percolation.CanonBurtonKeane
import Code.FK.FKLimitsErgodicUncond

open Set SimpleGraph Finset MeasureTheory
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

open Percolation
open FK

namespace Walls



theorem bins_exists_NineShellEvent_pos_measure
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure mu]
    (htop : 0 < mu {omega | numInfiniteClusters 2 omega = ⊤}) :
    ∃ (n : ℕ) (v u : Fin 9 → Site 2),
      0 < mu (bins_NineShellEvent n v u) := by
  obtain ⟨n, hn⟩ := Percolation.DisjointPaths.exists_pos_of_cover mu
    bins_iEqTop_subset_iUnion_NineMeetBox htop
  have hvcover : bins_NineMeetBox n ⊆
      ⋃ v : Fin 9 → Site 2, ⋃ u : Fin 9 → Site 2,
        bins_NineShellEvent n v u :=
    bins_NineMeetBox_subset_iUnion_NineShellEvent n
  obtain ⟨v, hv⟩ := Percolation.DisjointPaths.exists_pos_of_cover mu hvcover hn
  obtain ⟨u, hu⟩ := Percolation.DisjointPaths.exists_pos_of_cover mu
    (show (⋃ u : Fin 9 → Site 2, bins_NineShellEvent n v u) ⊆
        ⋃ u : Fin 9 → Site 2, bins_NineShellEvent n v u from fun _ h => h) hv
  exact ⟨n, v, u, hu⟩



theorem bins_setPattern_preimage_inter
    (I : Finset (Sym2 (Site 2))) (eta : ConfigSpace ↥I)
    (X : Set (ConfigSpace (Sym2 (Site 2))))
    (hX : DependsOn X ((↑I : Set (Sym2 (Site 2)))ᶜ)) :
    setPattern I eta ⁻¹'
        (cylinder I ({eta} : Set (ConfigSpace ↥I)) ∩ X) = X := by
  ext omega
  let target := setPattern I eta omega
  have hag : agreeOn ((↑I : Set (Sym2 (Site 2)))ᶜ) omega target := by
    intro e he
    have heI : e ∉ I := by simpa using he
    exact agreesOff_setPattern I eta omega e heI
  have hXiff : omega ∈ X ↔ target ∈ X := hX omega target hag
  constructor
  · rintro ⟨_, htX⟩
    exact hXiff.mpr htX
  · intro homega
    refine ⟨?_, hXiff.mp homega⟩
    change target ∈ cylinder I ({eta} : Set (ConfigSpace ↥I))
    rw [MeasureTheory.mem_cylinder, Set.mem_singleton_iff]
    exact setPattern_mem_patternEvent I eta omega



theorem bins_precursor_pos_of_patternAC
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure mu]
    (hpattern : ∀ (I : Finset (Sym2 (Site 2))) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu)
    (htop : 0 < mu {omega | numInfiniteClusters 2 omega = ⊤}) :
    ∃ a1 a2 a3 : Site 2, 0 < mu (NeighborTrifPrecursor 2 a1 a2 a3) := by
  obtain ⟨n, v, u, hnine⟩ := bins_exists_NineShellEvent_pos_measure mu htop
  obtain ⟨I, eta, a1, a2, a3, X, _hne, _hadj, hXmeas, hXdep, hXpos, hsub⟩ :=
    bins_routePackage_of_nineShell_measure mu n v u hnine
  let A : Set (ConfigSpace (Sym2 (Site 2))) :=
    cylinder I ({eta} : Set (ConfigSpace ↥I)) ∩ X
  have hAmeas : MeasurableSet A :=
    (bcl_cylinder_measurable I eta).inter hXmeas
  have hpre : setPattern I eta ⁻¹' A = X := by
    exact bins_setPattern_preimage_inter I eta X hXdep
  have hApos : 0 < mu A := by
    by_contra hnot
    rw [not_lt, nonpos_iff_eq_zero] at hnot
    have hzero := hpattern I eta hnot
    rw [Measure.map_apply (FK.measurable_setPattern I eta) hAmeas, hpre] at hzero
    exact (ne_of_gt hXpos) hzero
  exact ⟨a1, a2, a3, lt_of_lt_of_le hApos (measure_mono hsub)⟩

end Walls

namespace Percolation



theorem precursor_subset_force_canonical (a1 a2 a3 : Site d) :
    NeighborTrifPrecursor d a1 a2 a3 ⊆
      (fun omega => forceOpenFinset
        {s((0 : Site d), a1), s((0 : Site d), a2), s((0 : Site d), a3)} omega) ⁻¹'
        {omega | IsCanonicalTrifurcation d omega 0} := by
  intro omega homega
  obtain ⟨hne, ⟨hadj1, hadj2, hadj3⟩, hinf, hsep⟩ := homega
  let F : Finset (Sym2 (Site d)) :=
    {s((0 : Site d), a1), s((0 : Site d), a2), s((0 : Site d), a3)}
  let omega' := forceOpenFinset F omega
  have hFmem : ∀ e ∈ F, (0 : Site d) ∈ e := by
    intro e he
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h <;> (rw [h]; exact Sym2.mem_mk_left _ _)
  have hrm : removeSite (0 : Site d) omega' = removeSite 0 omega :=
    removeSite_forceOpen_eq 0 F hFmem omega
  have hopen1 : (openSubgraph d omega').Adj 0 a1 :=
    ⟨hadj1, forceOpenFinset_of_mem (by simp [F]) omega⟩
  have hopen2 : (openSubgraph d omega').Adj 0 a2 :=
    ⟨hadj2, forceOpenFinset_of_mem (by simp [F]) omega⟩
  have hopen3 : (openSubgraph d omega').Adj 0 a3 :=
    ⟨hadj3, forceOpenFinset_of_mem (by simp [F]) omega⟩
  change IsCanonicalTrifurcation d omega' 0
  refine ⟨a1, a2, a3, hne, ⟨hopen1, hopen2, hopen3⟩, ?_, ?_⟩
  · rw [hrm]
    exact hinf
  · rw [hrm]
    exact hsep



theorem canonicalTrif_pos_of_precursor_pos
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hfe : HasFiniteEnergyMerge mu) (a1 a2 a3 : Site d)
    (hpos : 0 < mu (NeighborTrifPrecursor d a1 a2 a3)) :
    0 < mu {omega | IsCanonicalTrifurcation d omega 0} := by
  let F : Finset (Sym2 (Site d)) :=
    {s((0 : Site d), a1), s((0 : Site d), a2), s((0 : Site d), a3)}
  by_contra hnot
  rw [not_lt, nonpos_iff_eq_zero] at hnot
  have hac := hfe F
  have hzero := hac hnot
  have hmap : mu.map (fun omega => forceOpenFinset F omega)
        {omega | IsCanonicalTrifurcation d omega 0} =
      mu ((fun omega => forceOpenFinset F omega) ⁻¹'
        {omega | IsCanonicalTrifurcation d omega 0}) :=
    Measure.map_apply (measurable_forceOpenFinset F)
      (ctp_measurableSet_isCanonicalTrifurcation 0)
  rw [hmap] at hzero
  have hle : mu (NeighborTrifPrecursor d a1 a2 a3) ≤
      mu ((fun omega => forceOpenFinset F omega) ⁻¹'
        {omega | IsCanonicalTrifurcation d omega 0}) :=
    measure_mono (precursor_subset_force_canonical a1 a2 a3)
  rw [hzero] at hle
  exact (ne_of_gt hpos) (le_antisymm hle bot_le)

end Percolation

namespace FK



theorem wiredInfinite_planar_canonicalTrif_pos_of_top_pos
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (htop : 0 < (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
      {omega | numInfiniteClusters 2 omega = ⊤}) :
    0 < (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
      {omega | IsCanonicalTrifurcation 2 omega 0} := by
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq)
  change 0 < mu {omega | IsCanonicalTrifurcation 2 omega 0}
  have htop' : 0 < mu {omega | numInfiniteClusters 2 omega = ⊤} := by
    simpa [mu] using htop
  obtain ⟨a1, a2, a3, hpre⟩ := Walls.bins_precursor_pos_of_patternAC mu
    (fun I eta => wiredInfinite_setPattern_absolutelyContinuous hp hp1 hq I eta) htop'
  exact canonicalTrif_pos_of_precursor_pos mu
    (wiredInfiniteVolume_hasFiniteEnergyMerge hp hp1 hq) a1 a2 a3 hpre



theorem freeInfinite_planar_canonicalTrif_pos_of_top_pos
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (htop : 0 < (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
      {omega | numInfiniteClusters 2 omega = ⊤}) :
    0 < (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
      {omega | IsCanonicalTrifurcation 2 omega 0} := by
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq)
  change 0 < mu {omega | IsCanonicalTrifurcation 2 omega 0}
  have htop' : 0 < mu {omega | numInfiniteClusters 2 omega = ⊤} := by
    simpa [mu] using htop
  obtain ⟨a1, a2, a3, hpre⟩ := Walls.bins_precursor_pos_of_patternAC mu
    (fun I eta => freeInfinite_setPattern_absolutelyContinuous hp hp1 hq I eta) htop'
  exact canonicalTrif_pos_of_precursor_pos mu
    (freeInfiniteVolume_hasFiniteEnergyMerge hp hp1 hq) a1 a2 a3 hpre




theorem wiredInfinite_planar_canonical_uniqueness_of_ergodic
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (herg : IsErgodic (G := Multiplicative (Site 2))
      (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2))))) :
    ((wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | numInfiniteClusters 2 omega = 0} = 1 ∨
      (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | numInfiniteClusters 2 omega = 1} = 1) ∧
      (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          (atLeastTwoInfinite 2) = 0 ∧
      (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | numInfiniteClusters 2 omega ≤ 1} = 1 := by
  exact cbk_canonical_uniqueness (d := 2)
    (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (by norm_num) herg (wiredInfiniteVolume_hasFiniteEnergyMerge hp hp1 hq)
    (wiredInfinite_planar_canonicalTrif_pos_of_top_pos hp hp1 hq)



theorem freeInfinite_planar_canonical_uniqueness_of_ergodic
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (herg : IsErgodic (G := Multiplicative (Site 2))
      (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2))))) :
    ((freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | numInfiniteClusters 2 omega = 0} = 1 ∨
      (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | numInfiniteClusters 2 omega = 1} = 1) ∧
      (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          (atLeastTwoInfinite 2) = 0 ∧
      (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | numInfiniteClusters 2 omega ≤ 1} = 1 := by
  exact cbk_canonical_uniqueness (d := 2)
    (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (by norm_num) herg (freeInfiniteVolume_hasFiniteEnergyMerge hp hp1 hq)
    (freeInfinite_planar_canonicalTrif_pos_of_top_pos hp hp1 hq)


theorem wiredInfinite_planar_q2_canonical_uniqueness
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ((wiredInfiniteVolume 2 hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | numInfiniteClusters 2 omega = 0} = 1 ∨
      (wiredInfiniteVolume 2 hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | numInfiniteClusters 2 omega = 1} = 1) ∧
      (wiredInfiniteVolume 2 hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          (atLeastTwoInfinite 2) = 0 ∧
      (wiredInfiniteVolume 2 hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | numInfiniteClusters 2 omega ≤ 1} = 1 := by
  exact wiredInfinite_planar_canonical_uniqueness_of_ergodic hp hp1
    (by norm_num : (1 : ℝ) ≤ 2) (feu_wiredIV_isErgodic (by norm_num) hp hp1)

end FK
end StatMech
