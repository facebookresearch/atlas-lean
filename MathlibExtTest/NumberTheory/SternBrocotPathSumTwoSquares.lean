/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.SternBrocotPathSumTwoSquares

/-! # Tests for sums of two squares from the Stern–Brocot tree -/

namespace MetaMathlibExt.sq_add_sq_of_sternBrocot_path

local notation "R" => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℕ)
local notation "L" => (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℕ)

private theorem rightMove_pow (k : ℕ) : R ^ k = !![1, k; 0, 1] := by
  induction k with
  | zero => exact Matrix.one_fin_two
  | succ k ih => simp [pow_succ, ih, Nat.add_comm]

private theorem leftMove_pow (k : ℕ) : L ^ k = !![1, 0; k, 1] := by
  induction k with
  | zero => exact Matrix.one_fin_two
  | succ k ih => simp [pow_succ, ih]

-- With `n = 0` the palindrome is `[k; k]`, the product of moves is empty and the path is
-- `R ^ (k - 1)`, with label `1 / k`.
example {p x₀ k : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (hx : (x₀ ^ 2 + 1) % p = 0)
    (hx₀ : 0 < x₀) (hxp : 2 * x₀ < p) (hk : 1 ≤ k) (hcf : (p : ℚ) / x₀ = k + (k : ℚ)⁻¹) :
    p = 1 + k ^ 2 := by
  have h := sq_add_sq_of_sternBrocot_path hp hp4 hx hx₀ hxp 0 (fun _ => k) (fun _ _ => hk)
    (by simpa [List.range_succ, List.bind_eq_flatMap, List.pure_def] using hcf)
  simpa [rightMove_pow, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Nat.sub_add_cancel hk]
    using h

-- With `n = 1` the palindrome is `[a; b, b, a]` and the path is `R ^ (a - 1) * L ^ b`, with
-- label `(a b + 1) / a`.
example {p x₀ a b : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (hx : (x₀ ^ 2 + 1) % p = 0)
    (hx₀ : 0 < x₀) (hxp : 2 * x₀ < p) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcf : (p : ℚ) / x₀ = a + (b + (b + (a : ℚ)⁻¹)⁻¹)⁻¹) :
    p = (a * b + 1) ^ 2 + a ^ 2 := by
  have h := sq_add_sq_of_sternBrocot_path hp hp4 hx hx₀ hxp 1
    (fun i => if i = 0 then a else b) (fun i _ => by split_ifs <;> assumption)
    (by simpa [List.range_succ, List.bind_eq_flatMap, List.pure_def] using hcf)
  obtain ⟨a, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  simp [rightMove_pow, leftMove_pow, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  rw [h]
  ring

-- The hypotheses hold for `p = 89` and `x₀ = 34`: `89 / 34 = [2; 1, 1, 1, 1, 1, 1, 2]` has
-- `n = 3`, the path is `R L R L` and its label `8 / 5` gives `89 = 8 ^ 2 + 5 ^ 2`.
example : (89 : ℕ) = 8 ^ 2 + 5 ^ 2 := by
  have h := sq_add_sq_of_sternBrocot_path (p := 89) (x₀ := 34) (by norm_num) rfl rfl
    (by norm_num) (by norm_num) 3 (fun i => if i = 0 then 2 else 1)
    (fun i _ => by split_ifs <;> norm_num)
    (by norm_num [List.range_succ, List.bind_eq_flatMap, List.pure_def])
  simp [List.range_succ, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Nat.even_iff,
    -Nat.reducePow] at h
  -- A closed equation would close the goal by evaluation: check the label syntactically.
  guard_hyp h :ₛ 89 = 8 ^ 2 + 5 ^ 2
  exact h

end MetaMathlibExt.sq_add_sq_of_sternBrocot_path
