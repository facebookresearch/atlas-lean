/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFolded
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFolded

/-- Folded counts at `n = 4`: `η₁ = ξ₁ + ξ₃` and `η₂ = ξ₂`. -/
example (ξ : ℕ → Unit → ℝ) :
    foldedCount 4 ξ 1 () = ξ 1 () + ξ 3 () ∧ foldedCount 4 ξ 2 () = ξ 2 () := by
  simp [foldedCount]

/-- Holding times for the `n = 4` example: `T₂ = 1/2`, `T₃ = 1/3`,
`T₄ = 1/7` (other values are irrelevant). -/
noncomputable def T4 : ℕ → ℝ := fun k =>
  match k with
  | 2 => 1 / 2
  | 3 => 1 / 3
  | 4 => 1 / 7
  | _ => 0

/-- The `n = 4` history `[[1,1,1,1], [1,1,2], [2,2], [4]]`: the SFS length
decomposition gives `2T₂ + 3T₃ + 4T₄ = 18 / 7`. -/
example :
    ∑ i ∈ Finset.Ico 1 4, ∑ k ∈ Finset.Icc 2 4,
        (([[1, 1, 1, 1], [1, 1, 2], [2, 2], [4]] :
          List (List ℕ)).getD (4 - k) []).count i * T4 k = 18 / 7 := by
  have hpos : ∀ k ∈ Finset.Icc 2 4,
      ∀ x ∈ ([[1, 1, 1, 1], [1, 1, 2], [2, 2], [4]] :
        List (List ℕ)).getD (4 - k) [], 1 ≤ x := by
    intro k hk
    obtain ⟨hk2, hk4⟩ := Finset.mem_Icc.mp hk
    interval_cases k <;> decide
  have hsum : ∀ k ∈ Finset.Icc 2 4,
      (([[1, 1, 1, 1], [1, 1, 2], [2, 2], [4]] :
        List (List ℕ)).getD (4 - k) []).sum = 4 := by
    intro k hk
    obtain ⟨hk2, hk4⟩ := Finset.mem_Icc.mp hk
    interval_cases k <;> decide
  have hlen : ∀ k ∈ Finset.Icc 2 4,
      (([[1, 1, 1, 1], [1, 1, 2], [2, 2], [4]] :
        List (List ℕ)).getD (4 - k) []).length = k := by
    intro k hk
    obtain ⟨hk2, hk4⟩ := Finset.mem_Icc.mp hk
    interval_cases k <;> decide
  rw [sum_sum_count_mul_eq_sum_mul _ T4 hpos hsum hlen]
  norm_num [T4, Finset.sum_Icc_succ_top]

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFolded
