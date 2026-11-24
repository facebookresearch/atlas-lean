/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosStrausDivisorPatterns
import Mathlib.Tactic.NormNum

/-! # Tests for the type I Erdős–Straus divisor criteria -/

open MetaMathlibExt

-- At the upper endpoint for p = 3, the first two denominators coincide.
example : ∃ y z : ℕ, y = 2 ∧ z = 3 ∧ ¬ 3 ∣ y := by
  obtain ⟨y, z, hy, hz, _, _, hpy⟩ := erdosStraus_typeI_of_dvd_sq
    (p := 3) (x := 2) (d := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  exact ⟨y, z, by omega, by omega, hpy⟩

-- At the lower endpoint for p = 13, the divisor 8 divides x² but does not divide px.
example : ∃ y z : ℕ, y = 20 ∧ z = 130 ∧ ¬ 13 ∣ y := by
  obtain ⟨y, z, hy, hz, _, _, hpy⟩ := erdosStraus_typeI_of_dvd_sq
    (p := 13) (x := 4) (d := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  exact ⟨y, z, by omega, by omega, hpy⟩

-- Conversely, the type I solution `(4, 20, 130)` for `p = 13` comes from the divisor 8 of 4².
example : ∃ d : ℕ, d = 8 ∧ d ∣ 4 ^ 2 := by
  obtain ⟨-, -, d, -, hd, -, hy, -⟩ := erdosStraus_typeI_exists_dvd_sq
    (p := 13) (x := 4) (y := 20) (z := 130) (by decide) (by decide) (by decide) (by decide)
    (by norm_num) (by decide)
  exact ⟨d, by omega, hd⟩

-- The type I solution `(4, 4, 14)` for `p = 7` attains the upper bound `x = ⌈7/2⌉`; here d = 2x.
example : ∃ d : ℕ, d = 8 ∧ d ∣ 4 ^ 2 := by
  obtain ⟨-, -, d, -, hd, -, hy, -⟩ := erdosStraus_typeI_exists_dvd_sq
    (p := 7) (x := 4) (y := 4) (z := 14) (by decide) (by decide) le_rfl (by decide)
    (by norm_num) (by decide)
  exact ⟨d, by omega, hd⟩

-- The bound `x ≤ ⌈p/2⌉` rules out `x = 5` for `p = 7`, although `1/5 < 4/7 ≤ 3/5`.
example (y z : ℕ) (hxy : 5 ≤ y) (hyz : y ≤ z) (hpy : ¬ 7 ∣ y) :
    (4 : ℚ) / 7 ≠ 1 / 5 + 1 / y + 1 / z := by
  intro h
  have := (erdosStraus_typeI_exists_dvd_sq (p := 7) (x := 5) (by decide) (by decide) hxy hyz
    (by exact_mod_cast h) hpy).2.1
  omega
