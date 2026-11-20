/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Percolation.BurtonKeaneUniqueness

open MeasureTheory
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}








def atLeastTwoInfinite (d : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | 2 ≤ numInfiniteClusters d ω}


theorem measurableSet_atLeastTwoInfinite :
    MeasurableSet (atLeastTwoInfinite d) := by
  have h : atLeastTwoInfinite d
      = (numInfiniteClusters d) ⁻¹' {k : ℕ∞ | 2 ≤ k} := rfl
  rw [h]
  exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)



theorem atLeastTwoInfinite_compl :
    (atLeastTwoInfinite d)ᶜ = {ω | numInfiniteClusters d ω ≤ 1} := by
  ext ω
  simp only [atLeastTwoInfinite, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  constructor
  · intro h; exact Order.le_of_lt_succ (by exact_mod_cast h)
  · intro h; exact lt_of_le_of_lt h (by decide)











theorem enat_le_one_of_not_two {k : ℕ∞} (h2 : ¬ (2 ≤ k)) : k ≤ 1 := by
  rw [not_le] at h2
  exact Order.le_of_lt_succ (by exact_mod_cast h2)







theorem numInfiniteClusters_le_one_of_const
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  
  
  have hknot2 : ¬ (2 ≤ k) := by
    intro h2
    have hsub : {ω | numInfiniteClusters d ω = k} ⊆ atLeastTwoInfinite d := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      exact (show 2 ≤ numInfiniteClusters d ω by rw [hω]; exact h2)
    have hle : μ {ω | numInfiniteClusters d ω = k} ≤ μ (atLeastTwoInfinite d) :=
      measure_mono hsub
    rw [hk, hmerge] at hle
    exact absurd hle (by norm_num)
  
  have hkle : k ≤ 1 := enat_le_one_of_not_two hknot2
  have hsub : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω ≤ 1} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω]; exact hkle
  exact le_antisymm prob_le_one (hk ▸ measure_mono hsub)























theorem infiniteCluster_unique_ae
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  exact numInfiniteClusters_le_one_of_const μ hk hmerge





























theorem burton_keane_uniqueness
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0})
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    ∃ k : ℕ∞, k ≤ 1 ∧ μ {ω | numInfiniteClusters d ω = k} = 1
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  
  obtain ⟨k, hktop, hk⟩ :=
    numInfiniteClusters_ae_const_ne_top μ herg bdry hbound hvol hdens htrif
  
  have hknot2 : ¬ (2 ≤ k) := by
    intro h2
    have hsub : {ω | numInfiniteClusters d ω = k} ⊆ atLeastTwoInfinite d := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      exact (show 2 ≤ numInfiniteClusters d ω by rw [hω]; exact h2)
    have hle : μ {ω | numInfiniteClusters d ω = k} ≤ μ (atLeastTwoInfinite d) :=
      measure_mono hsub
    rw [hk, hmerge] at hle
    exact absurd hle (by norm_num)
  refine ⟨k, enat_le_one_of_not_two hknot2, hk, ?_⟩
  exact numInfiniteClusters_le_one_of_const μ hk hmerge

end Percolation

end StatMech
