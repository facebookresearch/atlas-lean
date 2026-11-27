/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Finance.CRRCallPrice
import Mathlib.Tactic.NormNum

/-! # Tests for the Cox–Ross–Rubinstein call price -/

open MathlibExt.Probability.Finance.BinomialReplication
open MathlibExt.Probability.Finance.OptionPayoffs
open scoped BigOperators

-- At horizon zero the single node is in the money and no discount applies.
example : claimValue 2 (1 / 2) (5 / 4)
    (fun s => europeanCallPayoff (price 16 2 (1 / 2) s) 10) 0 [] = 6 := by
  obtain ⟨a, _, hcut, h, _⟩ := claimValue_call_eq_binomialTails
    (S₀ := 16) (u := 2) (d := 1 / 2) (R := 5 / 4) (K := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  have ha : a = 0 := Nat.eq_zero_of_le_zero ((hcut 0 (by decide)).mpr (by norm_num))
  dsimp only at h
  rw [ha, show Finset.Ico (0 : ℕ) 1 = {0} by decide] at h
  norm_num at h
  exact h

-- The terminal prices are 4, 16 and 64. The last two count, with weights at p = 1/2 and p' = 4/5.
example : claimValue 2 (1 / 2) (5 / 4)
    (fun s => europeanCallPayoff (price 16 2 (1 / 2) s) 10) 2 [] = 264 / 25 := by
  obtain ⟨a, _, hcut, h, _⟩ := claimValue_call_eq_binomialTails
    (S₀ := 16) (u := 2) (d := 1 / 2) (R := 5 / 4) (K := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2
  have hlo : ¬ a ≤ 0 := fun ha => by have := (hcut 0 (by decide)).mp ha; norm_num at this
  have hhi : a ≤ 1 := (hcut 1 (by decide)).mpr (by norm_num)
  have ha : a = 1 := by omega
  dsimp only at h
  rw [ha, show Finset.Ico (1 : ℕ) 3 = {1, 2} by decide] at h
  norm_num [rnProb, Finset.sum_insert, Nat.choose_one_right, Nat.choose_self] at h
  exact h

-- A strike equal to the highest terminal price excludes even the all-up path.
example : claimValue 2 (1 / 2) (5 / 4)
    (fun s => europeanCallPayoff (price 16 2 (1 / 2) s) 64) 2 [] = 0 := by
  obtain ⟨a, hbound, hcut, _, hzero⟩ := claimValue_call_eq_binomialTails
    (S₀ := 16) (u := 2) (d := 1 / 2) (R := 5 / 4) (K := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2
  have hlo : ¬ a ≤ 2 := fun ha => by
    have hlt := (hcut 2 (by decide)).mp ha
    norm_num at hlt
  exact hzero (by omega)
