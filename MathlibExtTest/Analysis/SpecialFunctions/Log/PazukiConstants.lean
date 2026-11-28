/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Log.PazukiConstants

open Real

-- Both inequalities for arbitrary `g ≥ 1` and `r ≥ 2`.
example (g r : ℕ) (hg : 1 ≤ g) (hr : 2 ≤ r) :
    (max |Pazuki.m r g| (Pazuki.M r g) + 3 / 2 + g / 4 * log (2 * π)) / log 3 +
        Pazuki.C g / 4 ≤ Pazuki.C₁ g r :=
  Pazuki.firstComparison_constant_le g r hg hr

example (g r : ℕ) (hg : 1 ≤ g) (hr : 2 ≤ r) :
    Pazuki.lemma57Constant (2 * Pazuki.C₁ g r) / 2 * (1 + log 2 / log 3) ≤ Pazuki.C₂ g r :=
  Pazuki.secondComparison_constant_le g r hg hr

-- The smallest case `g = 1`, `r = 2`, where `C₁(1, 2) = 24 log 4`.
example : (max |Pazuki.m 2 1| (Pazuki.M 2 1) + 3 / 2 + 1 / 4 * log (2 * π)) / log 3 +
    Pazuki.C 1 / 4 ≤ 24 * log 4 := by
  have := Pazuki.firstComparison_constant_le 1 2 le_rfl le_rfl
  simp only [Pazuki.C₁] at this
  norm_num at this ⊢
  linarith

-- The case `g = 2`, `r = 4` (Pazuki's Remark 1.6 suggests `r = 2` or `r = 4`).
example : Pazuki.lemma57Constant (2 * Pazuki.C₁ 2 4) / 2 * (1 + log 2 / log 3) ≤
    Pazuki.C₂ 2 4 :=
  Pazuki.secondComparison_constant_le 2 4 (by norm_num) (by norm_num)
