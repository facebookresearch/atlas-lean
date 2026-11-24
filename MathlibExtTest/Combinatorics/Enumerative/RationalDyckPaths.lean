/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RationalDyckPaths

/-! # Tests for the shifted bijection of rational Dyck path families -/

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
