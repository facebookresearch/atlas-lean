/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneErgodic

/-!
# Zero or one infinite cluster, conditional form

For an ergodic percolation measure on `ℤ^d` with `μ(N ≥ 2) = 0`, a.s. there is no infinite cluster
or a.s. there is exactly one.

## i. Overview

Combines the a.s. constancy of the number `N` of infinite clusters under an ergodic measure with
the hypothesis `μ(N ≥ 2) = 0` to obtain the dichotomy `μ(N = 0) = 1 ∨ μ(N = 1) = 1`. As in
`BurtonKeaneErgodic`, the hypothesis on `N ≥ 2` is assumed, not proved.

## ii. Key results

- `numInfiniteClusters_zero_or_one` : the dichotomy for ergodic measures with `μ(N ≥ 2) = 0`.

## iii. Table of contents

- A. The dichotomy

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121
  (1989).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. The dichotomy -/

lemma enat_zero_or_one_of_not_two {k : ℕ∞} (h2 : ¬ (2 ≤ k)) : k = 0 ∨ k = 1 := by
  have hlt2 : k < 2 := not_le.mp h2
  have hk1 : k ≤ 1 := Order.le_of_lt_succ (by exact_mod_cast hlt2)
  rcases eq_or_lt_of_le hk1 with heq | hlt
  · exact Or.inr heq
  · exact Or.inl (le_antisymm (Order.le_of_lt_succ (by exact_mod_cast hlt)) bot_le)

lemma merge_event_null_of_construct
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hmergeConstruct :
      0 < μ (atLeastTwoInfinite d) → μ (atLeastTwoInfinite d) = 0) :
    μ (atLeastTwoInfinite d) = 0 := by
  rcases eq_or_ne (μ (atLeastTwoInfinite d)) 0 with h0 | hpos
  · exact h0
  · exact hmergeConstruct (pos_iff_ne_zero.mpr hpos)

lemma numInfiniteClusters_zero_or_one_of_const
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1 := by
  have hknot2 : ¬ (2 ≤ k) := by
    intro h2
    have hsub : {ω | numInfiniteClusters d ω = k} ⊆ atLeastTwoInfinite d := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      exact (show 2 ≤ numInfiniteClusters d ω by rw [hω]; exact h2)
    have hle : μ {ω | numInfiniteClusters d ω = k} ≤ μ (atLeastTwoInfinite d) :=
      measure_mono hsub
    rw [hk, hmerge] at hle
    exact absurd hle (by norm_num)
  rcases enat_zero_or_one_of_not_two hknot2 with hk0 | hk1
  · left; rwa [hk0] at hk
  · right; rwa [hk1] at hk

/-- For an ergodic measure with `μ(N ≥ 2) = 0`, either a.s. `N = 0` or a.s. `N = 1`. -/
lemma numInfiniteClusters_zero_or_one
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1 := by
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  exact numInfiniteClusters_zero_or_one_of_const μ hk hmerge

lemma numInfiniteClusters_zero_or_one_of_mergeConstruct
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hmergeConstruct :
      0 < μ (atLeastTwoInfinite d) → μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1 :=
  numInfiniteClusters_zero_or_one μ herg
    (merge_event_null_of_construct μ hmergeConstruct)

end Percolation

end StatMech
