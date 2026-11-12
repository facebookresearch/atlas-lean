/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Producer.ProfitFunction

@[expose] public section

/-! Tests for `MathlibExt.Economics.Producer.ProfitFunction`: concrete instances with exact values. -/

namespace MathlibExtTest.Economics.Producer.ProfitFunction

open _root_.MathlibExt.Economics.Producer

/-- Test production set: two points in `Fin 2 → ℝ`. -/
def testY : Set (Fin 2 → ℝ) := {![0, 0], ![1, -1]}

/-- At prices `![3, 1]`, the point `![1, -1]` maximizes profit over `testY`. -/
theorem test_max_at_31 : IsProfitMax testY ![3, 1] ![1, -1] := by
  constructor
  · simp [testY]
  · intro y' hy'
    simp only [testY, Set.mem_insert_iff, Set.mem_singleton_iff] at hy'
    rcases hy' with rfl | rfl
    · show (![3, 1] : Fin 2 → ℝ) ⬝ᵥ ![0, 0] ≤ (![3, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, -1]
      norm_num [dotProduct, Fin.sum_univ_two]
    · exact le_refl _

/-- At prices `![1, 3]`, the point `![0, 0]` maximizes profit over `testY`. -/
theorem test_max_at_13 : IsProfitMax testY ![1, 3] ![0, 0] := by
  constructor
  · simp [testY]
  · intro y' hy'
    simp only [testY, Set.mem_insert_iff, Set.mem_singleton_iff] at hy'
    rcases hy' with rfl | rfl
    · exact le_refl _
    · show (![1, 3] : Fin 2 → ℝ) ⬝ᵥ ![1, -1] ≤ (![1, 3] : Fin 2 → ℝ) ⬝ᵥ ![0, 0]
      norm_num [dotProduct, Fin.sum_univ_two]

/-- Profit at `![3, 1]` over `testY` is exactly `2`. -/
theorem test_profitFn_31 : profitFn testY ![3, 1] = 2 := by
  rw [test_max_at_31.profitFn_eq]
  norm_num [dotProduct, Fin.sum_univ_two]

/-- Profit at `![1, 3]` over `testY` is exactly `0`. -/
theorem test_profitFn_13 : profitFn testY ![1, 3] = 0 := by
  rw [test_max_at_13.profitFn_eq]
  norm_num [dotProduct, Fin.sum_univ_two]

/-- `convexOn_profitFn` at the two test prices with weights `1/2, 1/2`: the midpoint profit
is at most `1/2 • 2 + 1/2 • 0 = 1`. -/
theorem test_convexOn_half :
    profitFn testY ((1/2 : ℝ) • (![3, 1] : Fin 2 → ℝ) + (1/2 : ℝ) • (![1, 3] : Fin 2 → ℝ))
      ≤ 1 := by
  obtain ⟨-, hle⟩ := convexOn_profitFn testY
  have hmem1 : (![3, 1] : Fin 2 → ℝ) ∈ profitDomain testY :=
    test_max_at_31.mem_profitDomain
  have hmem2 : (![1, 3] : Fin 2 → ℝ) ∈ profitDomain testY :=
    test_max_at_13.mem_profitDomain
  have h := hle hmem1 hmem2 (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  rw [test_profitFn_31, test_profitFn_13] at h
  rw [show (1/2 : ℝ) • 2 + (1/2 : ℝ) • (0 : ℝ) = 1 from by norm_num] at h
  exact h

/-- The finite-valued domain over the empty production set is empty, so `sSup ∅ = 0` is
never read as a profit. -/
theorem test_profitDomain_empty : profitDomain (∅ : Set (Fin 2 → ℝ)) = ∅ := by
  ext p
  simp only [profitDomain, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨y, hy⟩, -⟩
  simp at hy

end MathlibExtTest.Economics.Producer.ProfitFunction
