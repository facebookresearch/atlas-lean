/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Hypersequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! # Tests for hypersequences -/

open Finset MetaMathlibExt

-- Generation zero is the sequence itself.
example (a : ℕ → ℤ) (n : ℕ) : hypersequence a 0 n = a n := rfl

-- The hypersequences of the constant sequence one are binomial coefficients:
-- `a^{(3)}_2 = binom(2 + 3, 3) = 10`, evaluated by the kernel.
example : hypersequence (fun _ => (1 : ℕ)) 3 2 = 10 := by decide

-- In generation two the first term is counted once for each partial sum.
example (a : ℕ → ℤ) : hypersequence a 2 1 = 2 * a 0 + a 1 := by
  simp [hypersequence, sum_range_succ]
  ring

-- The values may lie in any additive commutative monoid; for singleton multisets the first
-- generation collects the indices seen so far.
example : hypersequence (fun k => ({k} : Multiset ℕ)) 1 2 = {0, 1, 2} := by decide

-- Every generation starts with the first term of the sequence; generation one is
-- `hypersequence_one_zero`.
example (a : ℕ → ℤ) (r : ℕ) : hypersequence a r 0 = a 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [hypersequence_succ, ih]

example (a : ℕ → ℤ) : hypersequence a 1 0 = a 0 := hypersequence_one_zero a
