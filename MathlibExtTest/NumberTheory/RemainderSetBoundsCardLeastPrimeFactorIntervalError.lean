/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RemainderSetBoundsCardLeastPrimeFactorIntervalError
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Tests for counting integers with a given least prime factor in an interval
-/

namespace MathlibExtTest.NumberTheory.RemainderSetBoundsCardLeastPrimeFactorIntervalError

open MetaMathlibExt Finset

-- With `a = 10`, `t = 6` and `p = 3`, the only integer counted is `15`: both the
-- count and the main term equal `1`, well within the error bound `2`.
example : |((((Icc (10 + 1) (10 + 6)).filter
    (fun m => 3 ∣ m ∧ ∀ q < 3, q.Prime → ¬ q ∣ m)).card : ℕ) : ℝ) - 1| ≤ 2 := by
  have hmain := card_leastPrimeFactor_interval_error (a := 10) (t := 6) (p := 3)
    (by decide) (by decide) (by decide)
  have hcard : ((Icc (10 + 1) (10 + 6)).filter
      (fun m => 3 ∣ m ∧ ∀ q < 3, q.Prime → ¬ q ∣ m)).card = 1 := by decide
  have hprod : ∏ q ∈ (Finset.range 3).filter Nat.Prime, (1 - 1 / (q : ℝ)) = 1 / 2 := by
    have hset : (Finset.range 3).filter Nat.Prime = {2} := by decide
    rw [hset]
    norm_num [Finset.prod_singleton]
  have hpi : Nat.primeCounting (3 - 1) = 1 := by decide
  have e1 : ((6 : ℕ) : ℝ) * (1 / ((3 : ℕ) : ℝ)) * (1 / 2) = 1 := by norm_num
  have e2 : (2 : ℝ) ^ (1 : ℕ) = 2 := by norm_num
  rw [hcard] at hmain ⊢
  rw [hprod, hpi, e1, e2] at hmain
  exact hmain

-- For `p = 2` there is no smaller prime, so the count is the even integers in the
-- interval and the main term is half the interval length.
example {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    |((((Icc (a + 1) (a + t)).filter (fun m => 2 ∣ m)).card : ℕ) : ℝ) - t / 2| ≤ 1 := by
  have hmain := card_leastPrimeFactor_interval_error (a := a) (t := t) (p := 2) ha ht
    Nat.prime_two
  have hfilter : (Icc (a + 1) (a + t)).filter
        (fun m => 2 ∣ m ∧ ∀ q < 2, q.Prime → ¬ q ∣ m)
      = (Icc (a + 1) (a + t)).filter (fun m => 2 ∣ m) := by
    apply Finset.filter_congr
    intro m _
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, fun q hq hprime => absurd hprime ?_⟩
      interval_cases q <;> decide
  have hprod : ∏ q ∈ (Finset.range 2).filter Nat.Prime, (1 - 1 / (q : ℝ)) = 1 := by
    have hset : (Finset.range 2).filter Nat.Prime = ∅ := by decide
    rw [hset, Finset.prod_empty]
  have hpi : Nat.primeCounting (2 - 1) = 0 := by decide
  have ecast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hfilter, hprod, hpi, mul_one, mul_one_div, pow_zero, ecast] at hmain
  exact hmain

end MathlibExtTest.NumberTheory.RemainderSetBoundsCardLeastPrimeFactorIntervalError
