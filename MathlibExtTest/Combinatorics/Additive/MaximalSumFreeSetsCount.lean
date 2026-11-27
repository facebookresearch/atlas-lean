/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.MaximalSumFreeSetsCount

open Finset
open MathlibExt.Combinatorics.GreenProblem1LargeSumFreeWanted (IsSumFree)
open MathlibExt.Combinatorics.MaximalSumFreeSetsCountErdosProblem877Wanted

example :
    Filter.Tendsto (fun n : ℕ => (maximalSumFreeCount n : ℝ) / 2 ^ ((n : ℝ) / 2))
      Filter.atTop (nhds 0) :=
  maximalSumFreeCountSmall_holds

-- The empty interval has one maximal sum-free set.
example : maximalSumFreeCount 0 = 1 := by
  simp [maximalSumFreeCount, IsSumFree, filter_singleton]

-- The two singletons are maximal because 1 + 1 = 2 rules out the full interval.
example : maximalSumFreeCount 2 = 2 := by
  classical
  have hIcc : Icc (1 : ℕ) 2 = {1, 2} := by decide
  have hpow : ({1, 2} : Finset ℕ).powerset = {∅, {1}, {2}, {1, 2}} := by decide
  have hcases {S : Finset ℕ} (hS : S ⊆ ({1, 2} : Finset ℕ)) :
      S = ∅ ∨ S = {1} ∨ S = {2} ∨ S = {1, 2} := by
    have h := mem_powerset.2 hS
    simpa only [hpow, mem_insert, mem_singleton] using h
  have h₁ : IsSumFree ({1} : Finset ℕ) := by
    simp [IsSumFree]
  have h₂ : IsSumFree ({2} : Finset ℕ) := by
    simp [IsSumFree]
  have h₁₂ : ¬ IsSumFree ({1, 2} : Finset ℕ) := fun h =>
    h 1 (by simp) 1 (by simp) (by decide)
  unfold maximalSumFreeCount
  rw [hIcc]
  calc
    _ = ({{1}, {2}} : Finset (Finset ℕ)).card := by
      congr 1
      ext S
      simp only [mem_filter, mem_powerset, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hS, hfree, hmax⟩
        rcases hcases hS with rfl | h | h | rfl
        · have hbad := hmax {1} (by simp) (empty_subset _) h₁
          simp at hbad
        · exact Or.inl h
        · exact Or.inr h
        · exact (h₁₂ hfree).elim
      · rintro (rfl | rfl)
        · refine ⟨by simp, h₁, fun B hB hsub hfree => ?_⟩
          rcases hcases hB with rfl | h | rfl | rfl
          · simp at hsub
          · exact h
          · simp at hsub
          · exact (h₁₂ hfree).elim
        · refine ⟨by simp, h₂, fun B hB hsub hfree => ?_⟩
          rcases hcases hB with rfl | rfl | h | rfl
          · simp at hsub
          · simp at hsub
          · exact h
          · exact (h₁₂ hfree).elim
    _ = 2 := by decide
