/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.Percolation.BurtonKeaneErgodic

open MeasureTheory
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}











theorem enat_zero_or_one_of_not_two {k : ℕ∞} (h2 : ¬ (2 ≤ k)) : k = 0 ∨ k = 1 := by
  have hlt2 : k < 2 := not_le.mp h2
  have hk1 : k ≤ 1 := Order.le_of_lt_succ (by exact_mod_cast hlt2)
  rcases eq_or_lt_of_le hk1 with heq | hlt
  · exact Or.inr heq
  · exact Or.inl (le_antisymm (Order.le_of_lt_succ (by exact_mod_cast hlt)) bot_le)































theorem merge_event_null_of_construct
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hmergeConstruct :
      0 < μ (atLeastTwoInfinite d) → μ (atLeastTwoInfinite d) = 0) :
    μ (atLeastTwoInfinite d) = 0 := by
  rcases eq_or_ne (μ (atLeastTwoInfinite d)) 0 with h0 | hpos
  · exact h0
  · exact hmergeConstruct (pos_iff_ne_zero.mpr hpos)














theorem numInfiniteClusters_zero_or_one_of_const
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1 := by
  
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
  
  rcases enat_zero_or_one_of_not_two hknot2 with hk0 | hk1
  · left; rwa [hk0] at hk
  · right; rwa [hk1] at hk


















theorem numInfiniteClusters_zero_or_one
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1 := by
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  exact numInfiniteClusters_zero_or_one_of_const μ hk hmerge








theorem numInfiniteClusters_zero_or_one_of_mergeConstruct
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hmergeConstruct :
      0 < μ (atLeastTwoInfinite d) → μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1 :=
  numInfiniteClusters_zero_or_one μ herg
    (merge_event_null_of_construct μ hmergeConstruct)






























theorem burton_keane_uniqueness_dichotomy
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
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1
      ∧ ∃ k : ℕ∞, (k = 0 ∨ k = 1) ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
  
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
  refine ⟨numInfiniteClusters_zero_or_one_of_const μ hk hmerge,
    infiniteCluster_unique_ae μ herg hmerge,
    ⟨k, enat_zero_or_one_of_not_two hknot2, hk⟩⟩

end Percolation

end StatMech
