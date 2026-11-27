/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RobinExceptionalCount

open MetaMathlibExt

-- The first half-integer above the strict lower cutoff still counts no integers.
example : robinExceptionalSet (5040 + 1 / 2) = ∅ := by
  classical
  have h : ⌊(5040 + 1 / 2 : ℝ)⌋₊ = 5040 :=
    (Nat.floor_eq_iff (by norm_num)).2 (by norm_num)
  rw [robinExceptionalSet, h, Finset.Ioc_self, Finset.filter_empty]

-- An integer upper endpoint above the cutoff is counted exactly when it fails the inequality.
example (n : ℕ) (hn : 5040 < n) :
    n ∈ robinExceptionalSet (n : ℝ) ↔
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) ≤
        (ArithmeticFunction.sigma 1 n : ℝ) := by
  classical
  simp [robinExceptionalSet, hn]
