/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Percolation.GeneralTrifurcationPattern
import Code.Percolation.HrouteDisjointPaths
import Code.Percolation.CanonTrifProb
import Code.FK.InfiniteFiniteEnergy

open Set MeasureTheory Finset
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Percolation

variable {d : ℕ}



theorem threeMeetBox_subset_pattern_trifurcations (n : ℕ) :
    threeMeetBox d n ⊆
      ⋃ eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n),
        ⋃ hub : Site d,
          StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta ⁻¹'
            {omega | IsTrifurcation d omega hub} := by
  intro omega homega
  obtain ⟨_, a, b, c, ha, hb, hc, hia, hib, hic, hab, hac, hbc⟩ := homega
  obtain ⟨eta, hub, htrif⟩ := three_sites_finite_pattern_trifurcation
    omega n a b c ha hb hc hia hib hic hab hac hbc
  exact Set.mem_iUnion.mpr ⟨eta, Set.mem_iUnion.mpr ⟨hub, htrif⟩⟩


theorem threeMeetBox_subset_pattern_canonical_trifurcations (n : ℕ) :
    threeMeetBox d n ⊆
      ⋃ eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n),
        ⋃ hub : Site d,
          StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta ⁻¹'
            {omega | IsCanonicalTrifurcation d omega hub} := by
  intro omega homega
  obtain ⟨_, a, b, c, ha, hb, hc, hia, hib, hic, hab, hac, hbc⟩ := homega
  obtain ⟨eta, hub, htrif⟩ := three_sites_finite_pattern_canonical_trifurcation
    omega n a b c ha hb hc hia hib hic hab hac hbc
  exact Set.mem_iUnion.mpr ⟨eta, Set.mem_iUnion.mpr ⟨hub, htrif⟩⟩



theorem trifurcation_pos_of_threeMeetBox_patternAC
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I),
      mu.map (StatMech.FK.setPattern I eta) ≪ mu)
    (n : ℕ) (hpos : 0 < mu (threeMeetBox d n)) :
    ∃ hub : Site d, 0 < mu {omega | IsTrifurcation d omega hub} := by
  classical
  let I := StatMech.Ising.bondFinsetTouch d n
  let B : ConfigSpace ↥I → Set (ConfigSpace (Sym2 (Site d))) := fun eta =>
    ⋃ hub : Site d,
      StatMech.FK.setPattern I eta ⁻¹' {omega | IsTrifurcation d omega hub}
  have hcover : threeMeetBox d n ⊆ ⋃ eta, B eta := by
    simpa only [I, B] using (threeMeetBox_subset_pattern_trifurcations (d := d) n)
  obtain ⟨eta, heta⟩ := DisjointPaths.exists_pos_of_cover mu hcover hpos
  have hself : (⋃ hub : Site d,
      StatMech.FK.setPattern I eta ⁻¹' {omega | IsTrifurcation d omega hub}) ⊆
      ⋃ hub : Site d,
        StatMech.FK.setPattern I eta ⁻¹' {omega | IsTrifurcation d omega hub} :=
    fun _ h => h
  obtain ⟨hub, hpre⟩ := DisjointPaths.exists_pos_of_cover mu hself heta
  refine ⟨hub, ?_⟩
  by_contra hnot
  rw [not_lt, nonpos_iff_eq_zero] at hnot
  have hzero := hpattern I eta hnot
  rw [Measure.map_apply (StatMech.FK.measurable_setPattern I eta)
    (measurableSet_isTrifurcation hub)] at hzero
  exact (ne_of_gt hpre) hzero



theorem canonical_trifurcation_pos_of_threeMeetBox_patternAC
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I),
      mu.map (StatMech.FK.setPattern I eta) ≪ mu)
    (n : ℕ) (hpos : 0 < mu (threeMeetBox d n)) :
    ∃ hub : Site d, 0 < mu {omega | IsCanonicalTrifurcation d omega hub} := by
  classical
  let I := StatMech.Ising.bondFinsetTouch d n
  let B : ConfigSpace ↥I → Set (ConfigSpace (Sym2 (Site d))) := fun eta ↦
    ⋃ hub : Site d,
      StatMech.FK.setPattern I eta ⁻¹' {omega | IsCanonicalTrifurcation d omega hub}
  have hcover : threeMeetBox d n ⊆ ⋃ eta, B eta := by
    simpa only [I, B] using
      (threeMeetBox_subset_pattern_canonical_trifurcations (d := d) n)
  obtain ⟨eta, heta⟩ := DisjointPaths.exists_pos_of_cover mu hcover hpos
  have hself : (⋃ hub : Site d,
      StatMech.FK.setPattern I eta ⁻¹'
        {omega | IsCanonicalTrifurcation d omega hub}) ⊆
      ⋃ hub : Site d,
        StatMech.FK.setPattern I eta ⁻¹'
          {omega | IsCanonicalTrifurcation d omega hub} := fun _ h ↦ h
  obtain ⟨hub, hpre⟩ := DisjointPaths.exists_pos_of_cover mu hself heta
  refine ⟨hub, ?_⟩
  by_contra hnot
  rw [not_lt, nonpos_iff_eq_zero] at hnot
  have hzero := hpattern I eta hnot
  rw [Measure.map_apply (StatMech.FK.measurable_setPattern I eta)
    (ctp_measurableSet_isCanonicalTrifurcation hub)] at hzero
  exact (ne_of_gt hpre) hzero





theorem trifurcation_at_origin_pos_of_patternAC
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I),
      mu.map (StatMech.FK.setPattern I eta) ≪ mu)
    (htop : 0 < mu {omega | numInfiniteClusters d omega = ⊤}) :
    0 < mu {omega | IsTrifurcation d omega 0} := by
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos mu htop
  obtain ⟨hub, hhub⟩ := trifurcation_pos_of_threeMeetBox_patternAC mu hpattern n hn
  rwa [trifurcationProb_const mu hinv hub] at hhub


theorem canonical_trifurcation_at_origin_pos_of_patternAC
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I),
      mu.map (StatMech.FK.setPattern I eta) ≪ mu)
    (htop : 0 < mu {omega | numInfiniteClusters d omega = ⊤}) :
    0 < mu {omega | IsCanonicalTrifurcation d omega 0} := by
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos mu htop
  obtain ⟨hub, hhub⟩ := canonical_trifurcation_pos_of_threeMeetBox_patternAC
    mu hpattern n hn
  rwa [ctp_canonicalTrifurcationProb_const mu hinv hub] at hhub

end StatMech.Percolation
