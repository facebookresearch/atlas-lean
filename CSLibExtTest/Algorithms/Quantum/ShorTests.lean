/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Shor

@[expose] public section

/-!
# Public API tests for Shor's factoring algorithm

These tests use only the topic entry point. The concrete examples show the
hypotheses of `exists_factor_of_order` are satisfiable: the lemma yields a
nontrivial factor in each case.
-/

namespace Cslib.Shor.Tests

/-- The textbook example: `7` has order `4` modulo `15`, `4` is even, and
`7 ^ 2 = 49 ≢ ±1 (mod 15)`, so the lemma yields a nontrivial factor of `15`. -/
example : ∃ d, d ∣ 15 ∧ 1 < d ∧ d < 15 :=
  exists_factor_of_order (N := 15) (a := 7) (r := 4) (by norm_num)
    (by norm_num) (by decide) ⟨2, rfl⟩ (by decide) (by decide)

/-- A second example: `2` has order `6` modulo `21`, `6` is even, and
`2 ^ 3 = 8 ≢ ±1 (mod 21)`, so the lemma yields a nontrivial factor of `21`. -/
example : ∃ d, d ∣ 21 ∧ 1 < d ∧ d < 21 :=
  exists_factor_of_order (N := 21) (a := 2) (r := 6) (by norm_num)
    (by norm_num) (by decide) ⟨3, rfl⟩ (by decide) (by decide)

/-- The factor is the computed `gcd`: for `N = 15`, `a = 7`, `r = 4` the lemma
is about `gcd (7 ^ 2 - 1) 15 = gcd 48 15 = 3`. -/
example : Nat.gcd (7 ^ (4 / 2) - 1) 15 ∣ 15 ∧ 1 < Nat.gcd (7 ^ (4 / 2) - 1) 15 ∧
    Nat.gcd (7 ^ (4 / 2) - 1) 15 < 15 :=
  gcd_factor_of_order (N := 15) (a := 7) (r := 4) (by norm_num)
    (by norm_num) (by decide) ⟨2, rfl⟩ (by decide) (by decide)

example : Nat.gcd (7 ^ (4 / 2) - 1) 15 = 3 := by decide

end Cslib.Shor.Tests
