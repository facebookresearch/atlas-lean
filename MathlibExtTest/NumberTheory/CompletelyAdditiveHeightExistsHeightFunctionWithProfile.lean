/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CompletelyAdditiveHeightExistsHeightFunctionWithProfile
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Tests for realizing a prescribed profile
-/

namespace MathlibExtTest.NumberTheory.CompletelyAdditiveHeightExistsHeightFunctionWithProfile

open MetaMathlibExt

-- The constant-one profile puts exactly one prime at heights one and two.
example : ∃ H : ℕ → ℕ, IsHeightFunction H ∧
    {p : ℕ | p.Prime ∧ H p = 1}.ncard = 1 ∧ {p : ℕ | p.Prime ∧ H p = 2}.ncard = 1 := by
  have hinf : {k : ℕ | 1 ≤ k ∧ (fun _ : ℕ => 1) k ≠ 0}.Infinite := by
    have hset : {k : ℕ | 1 ≤ k ∧ (fun _ : ℕ => 1) k ≠ 0} = Set.Ici 1 := by
      ext k
      simp
    rw [hset]
    exact Set.Ici_infinite 1
  obtain ⟨H, hH, hprof⟩ := exists_heightFunction_with_profile (fun _ => 1) hinf
  exact ⟨H, hH, hprof 1 le_rfl, hprof 2 (by decide)⟩

-- The predecessor profile has no prime at height one and two primes at height three.
example : ∃ H : ℕ → ℕ, IsHeightFunction H ∧
    {p : ℕ | p.Prime ∧ H p = 1}.ncard = 0 ∧ {p : ℕ | p.Prime ∧ H p = 3}.ncard = 2 := by
  have hinf : {k : ℕ | 1 ≤ k ∧ (fun k : ℕ => k - 1) k ≠ 0}.Infinite := by
    have hset : {k : ℕ | 1 ≤ k ∧ (fun k : ℕ => k - 1) k ≠ 0} = Set.Ici 2 := by
      ext k
      simp only [Set.mem_Ici]
      constructor
      · rintro ⟨h1, hne⟩
        simp only [ne_eq] at hne
        omega
      · intro h2
        refine ⟨by omega, ?_⟩
        simp only [ne_eq]
        omega
    rw [hset]
    exact Set.Ici_infinite 2
  obtain ⟨H, hH, hprof⟩ := exists_heightFunction_with_profile (fun k => k - 1) hinf
  have h1 : {p : ℕ | p.Prime ∧ H p = 1}.ncard = 0 := hprof 1 le_rfl
  have h3 : {p : ℕ | p.Prime ∧ H p = 3}.ncard = 2 := hprof 3 (by decide)
  exact ⟨H, hH, h1, h3⟩

end MathlibExtTest.NumberTheory.CompletelyAdditiveHeightExistsHeightFunctionWithProfile
