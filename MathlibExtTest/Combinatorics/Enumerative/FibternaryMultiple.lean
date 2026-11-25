/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.List.Infix
import MathlibExt.Combinatorics.Enumerative.FibternaryMultiple

/-! # Tests for Fibternary multiples -/

open MetaMathlibExt

example : ∃ m, 0 < m ∧ 1 ∣ m ∧ (∀ e ∈ Nat.digits 3 m, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 m :=
  exists_fibternary_multiple (n := 1) (hn := by decide)

example : ∃ m, 0 < m ∧ 6 ∣ m ∧ (∀ e ∈ Nat.digits 3 m, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 m :=
  exists_fibternary_multiple (n := 6) (hn := by decide)

-- The one-digit witness has no high-end padding in `Nat.digits`.
example : Nat.digits 3 1 = [1] := by decide

-- 90 is a positive multiple of 6 with both a separating zero and two units-end zeros.
example : Nat.digits 3 90 = [0, 0, 1, 0, 1] := by decide

example : 0 < 90 ∧ 6 ∣ 90 ∧ (∀ e ∈ Nat.digits 3 90, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 90 := by
  decide
