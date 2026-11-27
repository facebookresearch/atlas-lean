/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ExtendedContinuantSilentTermsTableOneModSix

/-! # Tests for the silent-term formulas on table (33), case σ ≡ 1 (mod 6) -/

namespace MathlibExtTest.NumberTheory.ExtendedContinuantSilentTermsTableOneModSix

open MetaMathlibExt

private def tableSequence (i : ℤ) : ℤ :=
  if i ≤ -4 then (if (-i) % 3 = 1 then -1 else 1)
  else if i = -3 then 4 else if i = -2 then 1 else if i = -1 then -1 else 3

-- At the first admissible order σ = 7, c₁ = 1 and c₂ = 0 give w = 1 ≠ 0.
example :
    -extendedContinuant tableSequence 2 (-4) - 3 * extendedContinuant tableSequence 3 (-4) ≠
      0 := by
  have h := silentTerms_table_one_mod_six tableSequence 7 (by decide) (by decide)
    1 0 (by decide) (by decide) (by decide) (by decide) (by
      intro m hm _
      simp [tableSequence, show -m ≤ -4 by omega])
  have hne := h.1
  norm_num [show tableSequence 0 = 3 by decide] at hne
  exact hne

-- On the same instance the numerator formula evaluates to 1.
example :
    -1 + extendedContinuant tableSequence 1 (-3) +
      3 * extendedContinuant tableSequence 2 (-3) = 1 := by
  have h := silentTerms_table_one_mod_six tableSequence 7 (by decide) (by decide)
    1 0 (by decide) (by decide) (by decide) (by decide) (by
      intro m hm _
      simp [tableSequence, show -m ≤ -4 by omega])
  have hnum := h.2
  norm_num [show tableSequence 0 = 3 by decide] at hnum
  have hw : -extendedContinuant tableSequence 2 (-4) -
      3 * extendedContinuant tableSequence 3 (-4) = 1 := by decide
  omega

end MathlibExtTest.NumberTheory.ExtendedContinuantSilentTermsTableOneModSix
