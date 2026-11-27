/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedHofstadterOrder

/-!
# Tests for generalized Hofstadter substitution words, prefix counts, and image lengths
-/

open MetaMathlibExt

example (k : ℕ) : hofCount k (· = 1) 0 = 0 := rfl

-- The one-letter alphabet gives a prefix consisting entirely of ones.
example : hofPrefix 1 5 = [1, 1, 1, 1, 1] ∧ hofCount 1 (· = 1) 5 = 5 := by decide

-- Extending the prefixes can turn a strict inequality into equality.
example : hofCount 3 (· = 1) 5 = 1 ∧ hofCount 2 (· = 1) 5 = 2 := by decide

example : hofCount 3 (· = 1) 8 = 3 ∧ hofCount 2 (· = 1) 8 = 3 := by decide

example (n : ℕ) : hofCount 3 (· = 1) n ≤ hofCount 2 (· = 1) n :=
  hofCount_one_succ_le (by decide : 1 ≤ 2) n

-- Two substitutions already distinguish the one-letter and two-letter alphabets.
example : (hofL 2)^[2] 1 = 3 ∧ (hofL 1)^[2] 1 = 4 := by decide

-- Equality can persist for a nonempty prefix and a positive iterate.
example : (hofL 3)^[2] 1 = 3 ∧ (hofL 2)^[2] 1 = 3 := by decide

example (j n : ℕ) : (hofL 3)^[j] n ≤ (hofL 2)^[j] n :=
  hofL_iterate_succ_le (by decide : 1 ≤ 2) j n

-- At the smallest positive boundary, the top letter itself is repeated.
example : (hofTauList 1)^[1] [1] = [1, 1] :=
  (hofTauList_iterate_self (k := 1) le_rfl 1).1 le_rfl

-- At the common endpoint the zero iterate supplies the final letter.
example {k : ℕ} (hk : 1 ≤ k) :
    (hofTauList k)^[k] [k] = (hofTauList k)^[k - 1] [k] ++ [k] := by
  simpa using (hofTauList_iterate_self hk k).2 le_rfl

-- Beyond the endpoint, the order of the two earlier words matters.
example : (hofTauList 3)^[4] [3] = [3, 1, 2, 3, 3, 1] :=
  (hofTauList_iterate_self (k := 3) (by decide) 4).2 (by decide)

-- The zero iterate brackets each positive threshold between consecutive naturals.
example (m : ℕ) (hm : 1 ≤ m) : ∃! n : ℕ, 1 ≤ n ∧ n - 1 < m ∧ m ≤ n := by
  simpa only [Function.iterate_zero, id_eq] using
    existsUnique_hofL_iterate_bracket (k := 2) (by decide) hm 0

-- The first bracket includes its upper endpoint, 4.
example (n : ℕ) (hn : 1 ≤ n ∧ (hofL 1)^[2] (n - 1) < 4 ∧ 4 ≤ (hofL 1)^[2] n) : n = 1 :=
  (existsUnique_hofL_iterate_bracket (k := 1) le_rfl (by decide : 1 ≤ 4) 2).unique hn (by decide)

-- The next bracket excludes 4 and contains 5.
example (n : ℕ) (hn : 1 ≤ n ∧ (hofL 1)^[2] (n - 1) < 5 ∧ 5 ≤ (hofL 1)^[2] n) : n = 2 :=
  (existsUnique_hofL_iterate_bracket (k := 1) le_rfl (by decide : 1 ≤ 5) 2).unique hn (by decide)
