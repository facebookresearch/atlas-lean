/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.InfiniteClusterCount

/-!
# At most one infinite cluster, conditional form

For an ergodic percolation measure on `ℤ^d`, if the event of at least two infinite clusters is
null, the number of infinite clusters is a.s. constant and at most one.

## i. Overview

The number of infinite clusters is a.s. a constant `k ∈ ℕ ∪ {∞}` under an ergodic measure. If
`μ(N ≥ 2) = 0` then `k ≤ 1`. The hypothesis `hmerge : μ(N ≥ 2) = 0` already implies
`μ(N ≤ 1) = 1`, so the content of the statements is only that `N` is a.s. constant.

## ii. Key results

- `numInfiniteClusters_le_one_of_const` : an a.s. constant `N` with `μ(N ≥ 2) = 0` is at most one.
- `infiniteCluster_unique_ae` : the ergodic form.

## iii. Table of contents

- A. The event of at least two infinite clusters
- B. Uniqueness

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

/-! ## A. The event of at least two infinite clusters -/

/-- The event that there are at least two infinite open clusters. -/
def atLeastTwoInfinite (d : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | 2 ≤ numInfiniteClusters d ω}

lemma measurableSet_atLeastTwoInfinite :
    MeasurableSet (atLeastTwoInfinite d) := by
  have h : atLeastTwoInfinite d
      = (numInfiniteClusters d) ⁻¹' {k : ℕ∞ | 2 ≤ k} := rfl
  rw [h]
  exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)

lemma atLeastTwoInfinite_compl :
    (atLeastTwoInfinite d)ᶜ = {ω | numInfiniteClusters d ω ≤ 1} := by
  ext ω
  simp only [atLeastTwoInfinite, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  constructor
  · intro h; exact Order.le_of_lt_succ (by exact_mod_cast h)
  · intro h; exact lt_of_le_of_lt h (by decide)

lemma enat_le_one_of_not_two {k : ℕ∞} (h2 : ¬ (2 ≤ k)) : k ≤ 1 := by
  rw [not_le] at h2
  exact Order.le_of_lt_succ (by exact_mod_cast h2)

/-! ## B. Uniqueness -/

lemma numInfiniteClusters_le_one_of_const
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
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
  have hkle : k ≤ 1 := enat_le_one_of_not_two hknot2
  have hsub : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω ≤ 1} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hω]; exact hkle
  exact le_antisymm prob_le_one (hk ▸ measure_mono hsub)

lemma infiniteCluster_unique_ae
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  exact numInfiniteClusters_le_one_of_const μ hk hmerge

end Percolation

end StatMech
