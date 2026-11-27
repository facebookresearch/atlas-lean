/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.LittlewoodOfford
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! # Tests for the sharp Littlewood–Offord bound -/

open Finset MathlibExt.Combinatorics.ScottishBook179Wanted

-- The binomial estimate at an even and an odd length: 10 * 252 ^ 2 ≤ 4 ^ 10 and 7 * 35 ^ 2 ≤ 4 ^ 7.
example : 10 * Nat.choose 10 5 ^ 2 ≤ 4 ^ 10 := mul_choose_half_sq_le_four_pow 10

example : 7 * Nat.choose 7 3 ^ 2 ≤ 4 ^ 7 := mul_choose_half_sq_le_four_pow 7

-- Specialize the uniform constant to one negative coefficient and an arbitrary admissible shift.
example : ∃ A : ℝ, ∀ c : ℝ, 1 ≤ |c| →
    ((univ.filter (fun ε : Fin 1 → Bool => |c + (if ε 0 then -1 else 1)| < 1)).card : ℝ)
      ≤ A * 2 := by
  obtain ⟨A, _, hA⟩ := littlewoodOffordSharpBound
  refine ⟨A, fun c hc => ?_⟩
  let a : Fin 2 → ℝ := Fin.cons c (fun _ => -1)
  have ha : ∀ i, 1 ≤ |a i| := Fin.cases (by simpa [a] using hc) (fun _ => by norm_num [a])
  simpa [a, apply_ite] using hA 1 le_rfl a ha

-- With two unit coefficients and shift one the possible values are -1, 1 and 3.
example : (univ.filter (fun ε : Fin 2 → Bool =>
    |1 + ∑ i, (if ε i then (1 : ℝ) else -1)| < 1)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ε
  cases h₀ : ε 0 <;> cases h₁ : ε 1 <;> norm_num [Fin.sum_univ_two, h₀, h₁]

-- For three unit coefficients, three distinct sign vectors give the same shifted sum of zero.
example : (univ.filter (fun ε : Fin 3 → Bool =>
    |1 + ∑ i, (if ε i then (1 : ℝ) else -1)| < 1)).card = 3 := by
  have heq (ε : Fin 3 → Bool) :
      |1 + ∑ i, (if ε i then (1 : ℝ) else -1)| < 1 ↔
        |1 + ∑ i, (if ε i then (1 : ℤ) else -1)| < 1 := by
    rw [← Int.cast_lt (R := ℝ)]
    push_cast
    rfl
  simp_rw [heq]
  decide
