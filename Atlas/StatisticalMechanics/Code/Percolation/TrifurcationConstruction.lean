/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Percolation.GridBoxConnected
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.BurtonKeaneMergeGeom

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}











theorem removeSite_forceOpen_eq (x : Site d) (F : Finset (Sym2 (Site d)))
    (hF : ∀ e ∈ F, x ∈ e) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite x (forceOpenFinset F ω) = removeSite x ω := by
  funext e
  unfold removeSite forceOpenFinset
  by_cases hx : x ∈ e
  · simp [hx]
  · simp only [hx, if_false]
    by_cases hef : e ∈ F
    · exact absurd (hF e hef) hx
    · simp [hef]


theorem removeSite_le (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite x ω ≤ ω := by
  intro e; unfold removeSite; by_cases hx : x ∈ e <;> simp [hx]





















theorem isTrifurcation_of_neighbors
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
    IsTrifurcation d
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
  
  have hconn1 : Connected d ω' 0 a₁ := by
    apply IsOpenEdge.connected; exact ⟨hadj1, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  have hconn2 : Connected d ω' 0 a₂ := by
    apply IsOpenEdge.connected; exact ⟨hadj2, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  have hconn3 : Connected d ω' 0 a₃ := by
    apply IsOpenEdge.connected; exact ⟨hadj3, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  
  have hle : removeSite (0:Site d) ω ≤ ω' := by rw [← hrm]; exact removeSite_le 0 ω'
  have hinf1' : (cluster d ω' a₁).Infinite := hinf1.mono (cluster_mono hle a₁)
  have hinf2' : (cluster d ω' a₂).Infinite := hinf2.mono (cluster_mono hle a₂)
  have hinf3' : (cluster d ω' a₃).Infinite := hinf3.mono (cluster_mono hle a₃)
  
  refine ⟨a₁, a₂, a₃, hne, ⟨hconn1, hconn2, hconn3⟩, ⟨hinf1', hinf2', hinf3'⟩, ?_⟩
  rw [hrm]
  exact ⟨hsep12, hsep13, hsep23⟩












def NeighborTrifPrecursor (d : ℕ) (a₁ a₂ a₃ : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    ((cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite) ∧
    (¬ Connected d (removeSite 0 ω) a₁ a₂ ∧ ¬ Connected d (removeSite 0 ω) a₁ a₃ ∧
      ¬ Connected d (removeSite 0 ω) a₂ a₃)}





theorem precursor_subset_force_trif (a₁ a₂ a₃ : Site d) :
    NeighborTrifPrecursor d a₁ a₂ a₃ ⊆
      (fun ω => forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω)
        ⁻¹' {ω | IsTrifurcation d ω 0} := by
  rintro ω ⟨hne, ⟨hadj1, hadj2, hadj3⟩, ⟨hinf1, hinf2, hinf3⟩, ⟨hsep12, hsep13, hsep23⟩⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  exact isTrifurcation_of_neighbors ω a₁ a₂ a₃ hne hadj1 hadj2 hadj3 hinf1 hinf2 hinf3
    hsep12 hsep13 hsep23








theorem trif_pos_of_precursor_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (a₁ a₂ a₃ : Site d)
    (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ {ω | IsTrifurcation d ω 0} := by
  set F : Finset (Sym2 (Site d)) :=
    {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} with hFdef
  by_contra h
  rw [not_lt, nonpos_iff_eq_zero] at h
  
  have hac : (μ.map (fun ω => forceOpenFinset F ω)) ≪ μ := hfe F
  have hpush : (μ.map (fun ω => forceOpenFinset F ω)) {ω | IsTrifurcation d ω 0}
      = μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | IsTrifurcation d ω 0}) :=
    Measure.map_apply (measurable_forceOpenFinset F) (measurableSet_isTrifurcation 0)
  have hpre0 : μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | IsTrifurcation d ω 0}) = 0 := by
    rw [← hpush]; exact hac h
  have hAle : μ (NeighborTrifPrecursor d a₁ a₂ a₃)
      ≤ μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | IsTrifurcation d ω 0}) :=
    measure_mono (precursor_subset_force_trif a₁ a₂ a₃)
  rw [hpre0] at hAle
  exact absurd (le_antisymm hAle bot_le) (ne_of_gt hpos)










theorem exists_three_distinct {α : Type*} {S : Set α} (h : S.encard = ⊤) :
    ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have h3 : (3 : ℕ∞) ≤ S.encard := by rw [h]; exact le_top
  obtain ⟨t, hts, ht3⟩ := Set.exists_subset_encard_eq h3
  rw [Set.encard_eq_three] at ht3
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht3
  exact ⟨a, b, c, hts (by simp), hts (by simp), hts (by simp), hab, hac, hbc⟩






def threeMeetBox (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | numInfiniteClusters d ω = ⊤ ∧
    ∃ x y z : Site d, x ∈ box d n ∧ y ∈ box d n ∧ z ∈ box d n ∧
      (cluster d ω x).Infinite ∧ (cluster d ω y).Infinite ∧ (cluster d ω z).Infinite ∧
      cluster d ω x ≠ cluster d ω y ∧ cluster d ω x ≠ cluster d ω z ∧
      cluster d ω y ≠ cluster d ω z}





theorem iEqTop_subset_iUnion_threeMeetBox :
    {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤}
      ⊆ ⋃ n, threeMeetBox d n := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  have hcard : (infiniteClusters d ω).encard = ⊤ := hω
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h12, h13, h23⟩ := exists_three_distinct hcard
  simp only [infiniteClusters, Set.mem_setOf_eq] at hC₁ hC₂ hC₃
  obtain ⟨hinf1, x, hxeq⟩ := hC₁
  obtain ⟨hinf2, y, hyeq⟩ := hC₂
  obtain ⟨hinf3, z, hzeq⟩ := hC₃
  have hxinf : (cluster d ω x).Infinite := by rw [← hxeq]; exact hinf1
  have hyinf : (cluster d ω y).Infinite := by rw [← hyeq]; exact hinf2
  have hzinf : (cluster d ω z).Infinite := by rw [← hzeq]; exact hinf3
  have hcl12 : cluster d ω x ≠ cluster d ω y := by rw [← hxeq, ← hyeq]; exact h12
  have hcl13 : cluster d ω x ≠ cluster d ω z := by rw [← hxeq, ← hzeq]; exact h13
  have hcl23 : cluster d ω y ≠ cluster d ω z := by rw [← hyeq, ← hzeq]; exact h23
  obtain ⟨n, hn⟩ := finite_subset_box ({x, y, z} : Set (Site d)) (Set.toFinite _)
  have hxbox : x ∈ box d n := hn (by simp)
  have hybox : y ∈ box d n := hn (by simp)
  have hzbox : z ∈ box d n := hn (by simp)
  exact Set.mem_iUnion.mpr ⟨n, hω, x, y, z, hxbox, hybox, hzbox, hxinf, hyinf, hzinf,
    hcl12, hcl13, hcl23⟩







theorem exists_threeMeetBox_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤}) :
    ∃ n : ℕ, 0 < μ (threeMeetBox d n) := by
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : μ (⋃ n, threeMeetBox d n) = 0 := by
    refine le_antisymm ?_ bot_le
    calc μ (⋃ n, threeMeetBox d n) ≤ ∑' n, μ (threeMeetBox d n) := measure_iUnion_le _
      _ = 0 := by simp [hcon]
  have hle : μ {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤}
      ≤ μ (⋃ n, threeMeetBox d n) :=
    measure_mono iEqTop_subset_iUnion_threeMeetBox
  rw [hunion0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hpos)


























theorem htrif_discharged
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hroute : ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0} := by
  intro htop
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos μ htop
  obtain ⟨a₁, a₂, a₃, hpre⟩ := hroute n hn
  exact trif_pos_of_precursor_pos μ hfe a₁ a₂ a₃ hpre



























theorem burton_keane_uniqueness_trif_route
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hroute : ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_full μ herg hfe bdry hbound hvol hdens
    (htrif_discharged μ hfe hroute)

end Percolation

end StatMech
