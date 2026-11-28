/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Probability.MarkovChain.BirthDeathBalance

/-! # Tests for normalized birth–death balance weights -/

open scoped BigOperators
open ProbabilityTheory

private def birth (n : ℕ) : ℝ := if n = 1 then 0 else 2

private def death (n : ℕ) : ℝ := if n = 0 then 0 else 4

private noncomputable def weights (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, birth i / death (i + 1)

private noncomputable def twoPointMass : ℕ → ℝ
  | 0 => 2 / 3
  | 1 => 1 / 3
  | _ + 2 => 0

-- A zero birth rate at state 1 cuts the support after states 0 and 1,
-- even though later birth rates are positive and no positivity is assumed at `death 0`.
example : (∀ n, 0 ≤ twoPointMass n) ∧ HasSum twoPointMass 1 ∧
    (∀ n, birth n * twoPointMass n = death (n + 1) * twoPointMass (n + 1)) := by
  have hb (n : ℕ) : 0 ≤ birth n := by
    unfold birth
    split <;> norm_num
  have hd (n : ℕ) : 0 < death (n + 1) := by simp [death]
  have h := birthDeathBalanceWeights_normalized birth death hb hd
  have hfinite : (∀ n, 1 < n → weights n = 0) ∧ Summable weights :=
    h.2 1 (by norm_num [birth])
  have hsum : ∑' n, weights n = 3 / 2 := by
    rw [tsum_eq_sum (s := Finset.range 2) (fun n hn ↦ hfinite.1 n (by simpa using hn))]
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, weights, birth, death]
  refine (h.1 twoPointMass).2 ⟨hfinite.2, ?_⟩
  change ∀ n, twoPointMass n = weights n / (∑' i, weights i)
  intro n
  rw [hsum]
  match n with
  | 0 => norm_num [twoPointMass, weights]
  | 1 => norm_num [twoPointMass, weights, birth, death, Finset.prod_range_succ]
  | n + 2 => simp [twoPointMass, hfinite.1 (n + 2) (by omega)]

-- Unit birth and death rates give a divergent weight series, so there is no normalized solution.
example (π : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ π n) (hsum : HasSum π 1)
    (hbalance : ∀ n, π n = π (n + 1)) : False := by
  have h := birthDeathBalanceWeights_normalized (fun _ ↦ 1) (fun _ ↦ 1)
    (fun _ ↦ zero_le_one) (fun _ ↦ zero_lt_one)
  have hs := ((h.1 π).1 ⟨hnonneg, hsum, by simpa only [one_mul] using hbalance⟩).1
  have hconst : Summable (fun _ : ℕ ↦ (1 : ℝ)) := by simpa using hs
  have : Finite ℕ := Finite.of_summable_const zero_lt_one hconst
  exact not_finite ℕ
