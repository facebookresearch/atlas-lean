/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosStrausDivisorPatterns

/-! # Tests for the type I Erdős–Straus divisor criterion -/

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
