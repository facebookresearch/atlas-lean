/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SupremumOfSelectorProcesses

open MathlibExt.Analysis.SupremumOfSelectorProcessesWanted.SupremumOfSelectorProcesses
open Finset MeasureTheory ProbabilityTheory unitInterval

-- In a two-point ground set this atom requires one success and one failure.
example (p : I) :
    (binomialSetDistribution Bool p).real {({true} : Set Bool)} = (p : ℝ) * (1 - p) := by
  rw [binomialSetDistribution, setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ]
  have hcompl : (Set.univ \ ({true} : Set Bool)) = {false} := by
    ext b
    cases b <;> simp
  rw [hcompl]
  simp only [Set.ncard_singleton, pow_one]

-- A singleton is a valid generator at the cutoff. The empty generator costs one.
example (p : I) : IsSmall p {({()} : Set Unit)} ↔ (p : ℝ) ≤ 2⁻¹ := by
  classical
  constructor
  · rintro ⟨G, hcover, hcost⟩
    obtain ⟨T, hT, hsub⟩ : ∃ T ∈ G, T ⊆ ({()} : Set Unit) := by
      simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using hcover (Set.mem_singleton _)
    have hsingle : (p : ℝ) ^ T.ncard ≤ 2⁻¹ := by
      refine le_trans ?_ hcost
      exact single_le_sum (fun U _ ↦ pow_nonneg (unitInterval.nonneg p) _)
        (Set.mem_toFinset.mpr hT)
    by_cases h : () ∈ T
    · have hT' : T = {()} := hsub.antisymm (Set.singleton_subset_iff.mpr h)
      simpa [hT'] using hsingle
    · have hT' : T = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun x ↦ by cases x; exact h)
      rw [hT', Set.ncard_empty, pow_zero] at hsingle
      norm_num at hsingle
  · intro hp
    refine ⟨{({()} : Set Unit)}, ?_, ?_⟩
    · simp
    · simpa using hp
