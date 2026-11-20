/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Percolation.GridBoxConnected

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}












def twoMeetBox (d n : ℕ) (k : ℕ∞) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | numInfiniteClusters d ω = k ∧
    ∃ x y : Site d, x ∈ box d n ∧ y ∈ box d n ∧
      (cluster d ω x).Infinite ∧ (cluster d ω y).Infinite ∧
      cluster d ω x ≠ cluster d ω y}






theorem twoMeetBox_subset_mergeWitness (n : ℕ) (k : ℕ∞) :
    twoMeetBox d n k ⊆ MergeWitness d (boxEdges d n) k := by
  rintro ω ⟨hkeq, x, y, hx, hy, hxinf, hyinf, hne⟩
  refine ⟨hkeq, x, y, hxinf, hyinf, hne, ?_⟩
  exact box_allOpen_connected ω hx hy





theorem iEqLevel_subset_iUnion_twoMeetBox {k : ℕ∞} (hk2 : 2 ≤ k) :
    {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k}
      ⊆ ⋃ n, twoMeetBox d n k := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  
  have hcard : (2 : ℕ∞) ≤ (infiniteClusters d ω).encard := by
    have heq : numInfiniteClusters d ω = (infiniteClusters d ω).encard := rfl
    rw [heq] at hω; rw [hω]; exact hk2
  have hnt : (infiniteClusters d ω).Nontrivial := by
    apply Set.one_lt_encard_iff_nontrivial.mp
    exact lt_of_lt_of_le (by decide : (1 : ℕ∞) < 2) hcard
  obtain ⟨C₁, hC₁mem, C₂, hC₂mem, hCne⟩ := hnt
  simp only [infiniteClusters, Set.mem_setOf_eq] at hC₁mem hC₂mem
  obtain ⟨hinf1, x, hxeq⟩ := hC₁mem
  obtain ⟨hinf2, y, hyeq⟩ := hC₂mem
  
  have hxinf : (cluster d ω x).Infinite := by rw [← hxeq]; exact hinf1
  have hyinf : (cluster d ω y).Infinite := by rw [← hyeq]; exact hinf2
  have hclne : cluster d ω x ≠ cluster d ω y := by rw [← hxeq, ← hyeq]; exact hCne
  
  obtain ⟨n, hn⟩ := finite_subset_box ({x, y} : Set (Site d)) (Set.toFinite _)
  have hxbox : x ∈ box d n := hn (Set.mem_insert x {y})
  have hybox : y ∈ box d n := hn (Set.mem_insert_of_mem x rfl)
  exact Set.mem_iUnion.mpr ⟨n, hω, x, y, hxbox, hybox, hxinf, hyinf, hclne⟩













theorem exists_twoMeetBox_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk2 : 2 ≤ k) (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    ∃ n : ℕ, 0 < μ (twoMeetBox d n k) := by
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  
  have hunion0 : μ (⋃ n, twoMeetBox d n k) = 0 := by
    refine le_antisymm ?_ bot_le
    calc μ (⋃ n, twoMeetBox d n k) ≤ ∑' n, μ (twoMeetBox d n k) :=
          measure_iUnion_le _
      _ = 0 := by simp [hcon]
  
  have hle : μ {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k}
      ≤ μ (⋃ n, twoMeetBox d n k) :=
    measure_mono (iEqLevel_subset_iUnion_twoMeetBox hk2)
  rw [hk, hunion0] at hle
  exact absurd hle (by norm_num)

















theorem hmergeGeom_discharged
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (k : ℕ∞) (hk2 : 2 ≤ k) (_hktop : k ≠ ⊤)
    (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k) := by
  obtain ⟨n, hpos⟩ := exists_twoMeetBox_pos μ hk2 hk
  refine ⟨boxEdges d n, lt_of_lt_of_le hpos ?_⟩
  exact measure_mono (twoMeetBox_subset_mergeWitness n k)























theorem burton_keane_uniqueness_full
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
      0 < μ {ω | IsTrifurcation d ω 0}) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_via_merge μ herg hfe bdry hbound hvol hdens htrif
    (fun k hk2 hktop hk => hmergeGeom_discharged μ k hk2 hktop hk)

end Percolation

end StatMech
