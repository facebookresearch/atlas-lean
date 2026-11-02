/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Primorial

@[expose] public section

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

open Nat

/-- **Extending the primorial bound leftward across an interval.** Let $a \le m \le b$ be
natural numbers, and write $n\#$ for the primorial of $n$ (the product of all primes
$p \le n$). If $10^a \cdot b\# \le 34^a$, then $10^m \cdot m\# \le 34^m$. -/
lemma theta34_of_interval {lo hi m : ℕ} (hlo : lo ≤ m) (hhi : m ≤ hi)
    (hend : 10 ^ lo * primorial hi ≤ 34 ^ lo) :
    10 ^ m * primorial m ≤ 34 ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlo
  calc
    10 ^ (lo + k) * primorial (lo + k) ≤ 10 ^ (lo + k) * primorial hi := by
      exact Nat.mul_le_mul_left _ (primorial_mono hhi)
    _ = (10 ^ lo * primorial hi) * 10 ^ k := by
      simp only [pow_add]
      ac_rfl
    _ ≤ 34 ^ lo * 10 ^ k := Nat.mul_le_mul_right _ hend
    _ ≤ 34 ^ lo * 34 ^ k := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
    _ = 34 ^ (lo + k) := (pow_add 34 lo k).symm

-- These closed endpoint inequalities are evaluated once each instead of once per integer.
set_option exponentiation.threshold 2048
set_option maxRecDepth 16384

section

lemma theta34_at_1 : 10 ^ 0 * primorial 1 ≤ 34 ^ 0 := by decide
lemma theta34_at_4 : 10 ^ 2 * primorial 4 ≤ 34 ^ 2 := by decide
lemma theta34_at_10 : 10 ^ 5 * primorial 10 ≤ 34 ^ 5 := by decide
lemma theta34_at_18 : 10 ^ 11 * primorial 18 ≤ 34 ^ 11 := by decide
lemma theta34_at_30 : 10 ^ 19 * primorial 30 ≤ 34 ^ 19 := by decide
lemma theta34_at_46 : 10 ^ 31 * primorial 46 ≤ 34 ^ 31 := by decide
lemma theta34_at_70 : 10 ^ 47 * primorial 70 ≤ 34 ^ 47 := by decide
lemma theta34_at_100 : 10 ^ 71 * primorial 100 ≤ 34 ^ 71 := by decide
lemma theta34_at_132 : 10 ^ 101 * primorial 132 ≤ 34 ^ 101 := by decide

end

end MathlibExt.NumberTheory.BreuschWanted.Internal
