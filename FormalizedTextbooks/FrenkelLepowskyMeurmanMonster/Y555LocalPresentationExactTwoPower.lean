/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Kernel-checkable binary exponentiation with its exact ordinary natural-power semantics. -/
module

public import Mathlib.Data.Nat.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact binary exponentiation of two, reducing the exponent by half at each source step. -/
def y322ExactTwoPower (n : ℕ) : ℕ :=
  if h : n = 0 then 1
  else
    let p := y322ExactTwoPower (n / 2)
    if n % 2 = 0 then p * p else p * p * 2
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- The finite binary exponentiation algorithm is exactly the ordinary natural power of two. -/
theorem y322ExactTwoPower_eq (n : ℕ) : y322ExactTwoPower n = 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      rw [y322ExactTwoPower]
      rfl
    · have hd : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      rw [y322ExactTwoPower, dite_eq_right hn, ih (n / 2) hd]
      by_cases hr : n % 2 = 0
      · rw [ite_eq_left hr, ← Nat.pow_add]
        congr 1
        omega
      · have hr1 : n % 2 = 1 := by omega
        rw [ite_eq_right hr, ← Nat.pow_add]
        have he : n = n / 2 + n / 2 + 1 := by omega
        exact (Nat.pow_succ 2 (n / 2 + n / 2)).symm.trans
          (congrArg (fun m : ℕ => 2 ^ m) he.symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
