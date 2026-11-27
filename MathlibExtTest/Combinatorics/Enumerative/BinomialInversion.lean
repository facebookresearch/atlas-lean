/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.BinomialInversion
import Mathlib.Data.Nat.Choose.Sum

open Finset MetaMathlibExt

-- Inverting `2 ^ n = ∑ C(n,k)` gives `∑ (-1)^(n-k) C(n,k) 2^k = 1`, that is `(2 - 1)^n = 1`.
example (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * 2 ^ k = 1 :=
  ((binomial_inversion_iff (fun n => 2 ^ n) fun _ => 1).mp (fun n => by
    simpa using (Nat.cast_inj (R := ℝ)).mpr (Nat.sum_range_choose n).symm) n).symm

-- The backward direction recovers the alternating sum of a row of Pascal's triangle from the
-- inverse transform of the indicator of `0`, which is `(-1)^n`.
example (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (-1) ^ k = if n = 0 then 1 else 0 :=
  ((binomial_inversion_iff (fun n => if n = 0 then 1 else 0) fun n => (-1) ^ n).mpr
    (fun n => by simp) n).symm

-- The first two inverse values: `v_0 = u_0` and `v_1 = u_1 - u_0`, with the sign on `u_0`.
example (u v : ℕ → ℝ) (h : ∀ n, u n = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * v k) :
    v 0 = u 0 ∧ v 1 = u 1 - u 0 := by
  have hinv := (binomial_inversion_iff u v).mp h
  refine ⟨by simpa using hinv 0, ?_⟩
  rw [hinv 1]
  simp [sum_range_succ]
  ring

-- A sequence is determined by its binomial transform.
example (u v w : ℕ → ℝ) (hv : ∀ n, u n = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * v k)
    (hw : ∀ n, u n = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * w k) : v = w := by
  funext n
  rw [(binomial_inversion_iff u v).mp hv n, (binomial_inversion_iff u w).mp hw n]
