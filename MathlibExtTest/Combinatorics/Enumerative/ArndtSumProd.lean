/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtSumProd

open MetaMathlibExt

-- One pair: the only tuple is `(n)`, so `a(n, 2) = ⌊(n - 1)/2⌋` for every `n`; the filter
-- `3 ≤ n` only drops the weights `n ≤ 2`, where the factor already vanishes.
example (n : ℕ) : arndtCompositionCount (fun _ => True) n 2 = (n - 1) / 2 := by
  rw [(arndtCompositionCount_eq_sum_prod n 1).1]
  simp only [Finset.Nat.antidiagonalTuple_one, Finset.filter_singleton, Fin.forall_fin_one,
    Matrix.cons_val_fin_one, Fin.prod_univ_one]
  split_ifs with h
  · simp
  · simp only [Finset.sum_empty]
    omega

-- No pair and an odd number of parts: a single part, which must be positive.
example (n : ℕ) : arndtCompositionCount (fun _ => True) n 1 = if n = 0 then 0 else 1 := by
  rw [(arndtCompositionCount_eq_sum_prod n 0).2]
  rcases n with _ | n <;> simp [Finset.Nat.antidiagonalTuple_one, Finset.filter_singleton]

-- The single tuple `(3, 3)` gives the Arndt composition `(2, 1, 2, 1)` of 6.
example : arndtCompositionCount (fun _ => True) 6 4 = 1 := by
  rw [(arndtCompositionCount_eq_sum_prod 6 2).1]
  decide

-- The tuples `(3, 3)`, `(4, 2)` and `(5, 1)` contribute `1 + 1 + 2`: the Arndt compositions
-- `(2, 1, 3)`, `(3, 1, 2)`, `(3, 2, 1)` and `(4, 1, 1)` of 6.
example : arndtCompositionCount (fun _ => True) 6 3 = 4 := by
  rw [(arndtCompositionCount_eq_sum_prod 6 1).2]
  decide

-- Two pairs of weight 10: `(3, 7), (4, 6), (5, 5), (6, 4), (7, 3)` give `3 + 2 + 4 + 2 + 3 = 14`.
example : arndtCompositionCount (fun _ => True) 10 4 = 14 := by
  rw [(arndtCompositionCount_eq_sum_prod 10 2).1]
  decide

-- Two pairs and a last part of weight 9: `(3, 3, 3), (3, 4, 2), (4, 3, 2), (3, 5, 1), (5, 3, 1)`
-- and `(4, 4, 1)` give `1 + 1 + 1 + 2 + 2 + 1 = 8`.
example : arndtCompositionCount (fun _ => True) 9 5 = 8 := by
  rw [(arndtCompositionCount_eq_sum_prod 9 2).2]
  decide

-- Below weight `3ℓ` no tuple has all `ℓ` entries at least 3, so there is no composition.
example : arndtCompositionCount (fun _ => True) 8 6 = 0 := by
  rw [(arndtCompositionCount_eq_sum_prod 8 3).1]
  decide
