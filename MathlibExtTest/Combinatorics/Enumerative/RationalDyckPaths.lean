/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RationalDyckPaths

/-!
# Tests for the shifted correspondences between rational Dyck path families
-/

open MetaMathlibExt

-- The empty source path corresponds to the all-valley block word of length two.
example : (qBonacciDyckPaths 2 5 0).card = 1 ∧ (tildeRationalDyckPaths 2 5 3).card = 1 := by
  decide +kernel

-- At r = 2, s = 3 the admissible source words of length two are 00, 01 and 11.
example : (qBonacciDyckPaths 2 3 3).card = 3 ∧ (tildeRationalDyckPaths 2 3 5).card = 3 := by
  decide +kernel

-- A maximal final peak run can have too few valleys, even with a nonempty valley suffix.
example : IsQBonacciRuns 2 3 (boolRuns [true, true, false]) ∧
    ¬ IsTildeRationalRuns 2 3 (boolRuns [true, true, false]) := by
  decide

-- With t = 0 the shift is one semilength.
example (n : ℕ) : Nonempty (qBonacciDyckPaths 1 1 n ≃ tildeRationalDyckPaths 1 1 (n + 1)) :=
  nonempty_equiv_qBonacci_tildeRational (t := 0) (by decide) rfl n

-- With r = 2 and s = 3 the shift is two, including for the empty path.
example : (qBonacciDyckPaths 2 3 0).card = 1 ∧ (tildeRationalDyckPaths 2 3 2).card = 1 := by
  decide +kernel

-- A single terminal peak can use the exception. Adding just one valley removes it.
example : IsQBonacciRuns 2 3 (boolRuns [true]) ∧
    ¬ IsTildeRationalRuns 2 3 (boolRuns [true]) ∧
    ¬ IsQBonacciRuns 2 3 (boolRuns [true, false]) := by
  decide

-- At r = 1 every positive denominator satisfies the criterion.
example (n : ℕ) : Nonempty (tildeRationalDyckPaths 1 3 (n + 2 + 1) ≃ qBonacciDyckPaths 1 3 n) :=
  (forall_nonempty_equiv_qBonacci_tildeRational_iff (r := 1) (s := 3)
    (by decide) (by decide) (by decide)).2 (by decide) n

-- For r = 3, s = 2 the exceptional choice really does produce different counts.
example : (tildeRationalDyckPaths 3 2 5).card < (qBonacciDyckPaths 3 2 4).card := by
  obtain ⟨hq, hr⟩ := card_qBonacciDyckPaths_three_two_four
  omega
