/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Mathlib
import Code.Walls.bc48classical
import Code.Percolation.TrifurcationConstruction
import Code.Percolation.HrouteHighDim
import Code.Percolation.TrifurcationExistence
import Code.Percolation.TrifurcationFiniteEnergy

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}




























theorem bc49_isClassicalTrifurcation_of_neighbors
    (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj1 : (hypercubicLattice d).Adj 0 a₁)
    (hadj2 : (hypercubicLattice d).Adj 0 a₂)
    (hadj3 : (hypercubicLattice d).Adj 0 a₃)
    (hinf1 : (cluster d (removeSite 0 ω) a₁).Infinite)
    (hinf2 : (cluster d (removeSite 0 ω) a₂).Infinite)
    (hinf3 : (cluster d (removeSite 0 ω) a₃).Infinite)
    (hsep12 : ¬ Connected d (removeSite 0 ω) a₁ a₂)
    (hsep13 : ¬ Connected d (removeSite 0 ω) a₁ a₃)
    (hsep23 : ¬ Connected d (removeSite 0 ω) a₂ a₃) :
    bc47_IsClassicalTrifurcation
      (forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω) 0 := by
  classical
  set F : Finset (Sym2 (Site d)) :=
    {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} with hFdef
  set ω' := forceOpenFinset F ω with hω'
  
  have hFmem : ∀ e ∈ F, (0 : Site d) ∈ e := by
    intro e he
    simp only [hFdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h <;> (rw [h]; exact Sym2.mem_mk_left _ _)
  
  have hrm : removeSite (0:Site d) ω' = removeSite (0:Site d) ω :=
    removeSite_forceOpen_eq 0 F hFmem ω
  
  have hopen1 : IsOpenEdge d ω' 0 a₁ :=
    ⟨hadj1, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  have hopen2 : IsOpenEdge d ω' 0 a₂ :=
    ⟨hadj2, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  have hopen3 : IsOpenEdge d ω' 0 a₃ :=
    ⟨hadj3, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  
  refine ⟨a₁, a₂, a₃, hne, ⟨hopen1, hopen2, hopen3⟩, ?_, ?_⟩
  · rw [hrm]; exact ⟨hinf1, hinf2, hinf3⟩
  · rw [hrm]; exact ⟨hsep12, hsep13, hsep23⟩













theorem bc49_precursor_subset_force_classicalTrif (a₁ a₂ a₃ : Site d) :
    NeighborTrifPrecursor d a₁ a₂ a₃ ⊆
      (fun ω => forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω)
        ⁻¹' {ω | bc47_IsClassicalTrifurcation ω 0} := by
  rintro ω ⟨hne, ⟨hadj1, hadj2, hadj3⟩, ⟨hinf1, hinf2, hinf3⟩, ⟨hsep12, hsep13, hsep23⟩⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  exact bc49_isClassicalTrifurcation_of_neighbors ω a₁ a₂ a₃ hne hadj1 hadj2 hadj3
    hinf1 hinf2 hinf3 hsep12 hsep13 hsep23




theorem bc49_classicalTrif_of_precursor_mem (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d) (hω : ω ∈ NeighborTrifPrecursor d a₁ a₂ a₃) :
    bc47_IsClassicalTrifurcation
      (forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω) 0 :=
  bc49_precursor_subset_force_classicalTrif a₁ a₂ a₃ hω



















theorem bc49_classicalTrif_pos_of_precursor_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (a₁ a₂ a₃ : Site d)
    (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
  classical
  set F : Finset (Sym2 (Site d)) :=
    {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} with hFdef
  by_contra h
  rw [not_lt, nonpos_iff_eq_zero] at h
  
  have hac : (μ.map (fun ω => forceOpenFinset F ω)) ≪ μ := hfe F
  have hpush : (μ.map (fun ω => forceOpenFinset F ω)) {ω | bc47_IsClassicalTrifurcation ω 0}
      = μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | bc47_IsClassicalTrifurcation ω 0}) :=
    Measure.map_apply (measurable_forceOpenFinset F)
      (bc48_measurableSet_isClassicalTrifurcation 0)
  have hpre0 : μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | bc47_IsClassicalTrifurcation ω 0}) = 0 := by
    rw [← hpush]; exact hac h
  have hAle : μ (NeighborTrifPrecursor d a₁ a₂ a₃)
      ≤ μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | bc47_IsClassicalTrifurcation ω 0}) :=
    measure_mono (bc49_precursor_subset_force_classicalTrif a₁ a₂ a₃)
  rw [hpre0] at hAle
  exact absurd (le_antisymm hAle bot_le) (ne_of_gt hpos)




















theorem bc49_classical_htrif_of_route
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hroute : ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
  intro htop
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos μ htop
  obtain ⟨a₁, a₂, a₃, hpre⟩ := hroute n hn
  exact bc49_classicalTrif_pos_of_precursor_pos μ hfe a₁ a₂ a₃ hpre






theorem bc49_classical_htrif_of_routingCover
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | bc47_IsClassicalTrifurcation ω 0} :=
  bc49_classical_htrif_of_route μ hfe (hrHD_route_of_routing μ hfe hrt)






















theorem bc49_burton_keane_bernoulli_of_route (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_ClassicalBoundaryArmInjection ω n)
    (hroute : ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc48_burton_keane_bernoulli_of_classicalInjection hd p hp1 hp0 hinj
    (bc49_classical_htrif_of_route (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
      (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) hroute)





theorem bc49_burton_keane_bernoulli_of_routingCover (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_ClassicalBoundaryArmInjection ω n)
    (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc49_burton_keane_bernoulli_of_route hd p hp1 hp0 hinj
    (hrHD_route_of_routing (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
      (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) hrt)



















theorem bc49_precursor_forces_classicalTrif_genuinelyUsesFiniteEnergy
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (a₁ a₂ a₃ : Site d)
    (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ {ω | bc47_IsClassicalTrifurcation ω 0} :=
  bc49_classicalTrif_pos_of_precursor_pos μ hfe a₁ a₂ a₃ hpos






theorem bc49_precursor_nonvacuous (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
    (hd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
    (hd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
    (hd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    bc47_IsClassicalTrifurcation
      (forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω) 0 := by
  
  have hsep : ∀ b c : Site d, cluster d (removeSite 0 ω) b ≠ cluster d (removeSite 0 ω) c →
      ¬ Connected d (removeSite 0 ω) b c := by
    intro b c hbc hcon
    exact hbc (cluster_eq_of_connected hcon)
  exact bc49_isClassicalTrifurcation_of_neighbors ω a₁ a₂ a₃ hne hadj.1 hadj.2.1 hadj.2.2
    hi1 hi2 hi3 (hsep a₁ a₂ hd12) (hsep a₁ a₃ hd13) (hsep a₂ a₃ hd23)

end StatMech.Walls
