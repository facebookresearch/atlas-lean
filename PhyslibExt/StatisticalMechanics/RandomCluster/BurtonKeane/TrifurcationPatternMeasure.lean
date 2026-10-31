/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GeneralTrifurcationPattern
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonTrifProb
public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteFiniteEnergy

/-!
# Trifurcations of positive probability from finite patterns

If finite box patterns are absolutely continuous under the measure, three distinct infinite clusters
meeting a box give a canonical trifurcation at the origin with positive probability.

## i. Overview

Every configuration in `threeMeetBox d n` can be modified on the bonds touching `B_n` to have a
(canonical) trifurcation in the box (`GeneralTrifurcationPattern`). If setting such patterns
preserves null sets (pattern absolute continuity), positive probability of `threeMeetBox d n` gives
a trifurcation in the box with positive probability, and translation invariance moves it to the
origin.

## ii. Key results

- `threeMeetBox_subset_pattern_canonical_trifurcations` : box patterns produce canonical
  trifurcations
- `canonical_trifurcation_pos_of_threeMeetBox_patternAC` : positive probability of a canonical
  trifurcation in the box
- `canonical_trifurcation_at_origin_pos_of_patternAC` : positive probability of a canonical
  trifurcation at the origin

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set MeasureTheory Finset
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma threeMeetBox_subset_pattern_trifurcations (n : ℕ) :
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

lemma threeMeetBox_subset_pattern_canonical_trifurcations (n : ℕ) :
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

lemma trifurcation_pos_of_threeMeetBox_patternAC
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

lemma canonical_trifurcation_pos_of_threeMeetBox_patternAC
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

lemma trifurcation_at_origin_pos_of_patternAC
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I),
      mu.map (StatMech.FK.setPattern I eta) ≪ mu)
    (htop : 0 < mu {omega | numInfiniteClusters d omega = ⊤}) :
    0 < mu {omega | IsTrifurcation d omega 0} := by
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos mu htop
  obtain ⟨hub, hhub⟩ := trifurcation_pos_of_threeMeetBox_patternAC mu hpattern n hn
  rwa [trifurcationProb_const mu hinv hub] at hhub

lemma canonical_trifurcation_at_origin_pos_of_patternAC
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
