/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PracticalPolygonalSums
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! # Tests for bounded square roots modulo powers of two -/

open MetaMathlibExt

-- At the smallest exponent the interval forces the root to be 1.
example (n : ℕ) (hn : 0 < n) : 1 ≡ 8 * n + 1 [MOD 8] := by
  obtain ⟨x, hlo, hhi, hsq⟩ := exists_sq_modEq_eight_mul_add_one 1 n (by decide) hn
  have hx : x = 1 := by omega
  subst x
  exact hsq

-- The upper endpoint is necessary for 17 modulo 32.
example : (∃ x : ℕ, x ≤ 7 ∧ x ^ 2 ≡ 17 [MOD 32]) ∧
    ¬ ∃ x : ℕ, x < 7 ∧ x ^ 2 ≡ 17 [MOD 32] := by
  constructor
  · obtain ⟨x, _, hhi, hsq⟩ := exists_sq_modEq_eight_mul_add_one 3 2 (by decide) (by decide)
    exact ⟨x, hhi, hsq⟩
  · rintro ⟨x, hx, hsq⟩
    interval_cases x <;> norm_num [Nat.ModEq] at hsq
