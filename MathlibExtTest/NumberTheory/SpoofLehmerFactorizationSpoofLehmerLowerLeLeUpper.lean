/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SpoofLehmerFactorizationSpoofLehmerLowerLeLeUpper
import Mathlib.Tactic.NormNum

/-!
# Tests for Lehmer bounds at initial segments

For the spoof factorization `3 · 3`, the empty and one-base prefixes have lower bound strictly
below two, while the full prefix has lower bound two.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 3 and Table 1.
-/

namespace MathlibExtTest.NumberTheory.SpoofLehmerFactorizationSpoofLehmerLowerLeLeUpper

open MetaMathlibExt

example : lehmerLower [] 2 < 2 ∧ lehmerLower [3] 2 < 2 ∧
    lehmerLower [3, 3] 2 = 2 ∧ (2 : ℝ) ≤ lehmerUpper [3] 2 := by
  have hL : IsSpoofLehmer 2 (spoofOfBases ([3, 3] : List ℕ)) := by
    simpa [spoofOfBases, ← Multiset.cons_coe] using isSpoofLehmer_three_three
  have hnt : ¬ IsTrivialSpoof (spoofOfBases ([3, 3] : List ℕ)) := by
    simp [IsTrivialSpoof, spoofOfBases]
  have h := (spoofLehmer_lower_le_le_upper [3, 3] (by norm_num) 2 hL hnt).1
  have h0 : lehmerLower [] 2 ≤ 2 ∧ (2 : ℝ) ≤ lehmerUpper [] 2 ∧
      (lehmerLower [] 2 = 2 ↔ (0 : ℕ) = 2) := by simpa using h 0 (by decide)
  have h1 : lehmerLower [3] 2 ≤ 2 ∧ (2 : ℝ) ≤ lehmerUpper [3] 2 ∧
      (lehmerLower [3] 2 = 2 ↔ (1 : ℕ) = 2) := by simpa using h 1 (by decide)
  have h2 : lehmerLower [3, 3] 2 = 2 := by
    simpa using (h 2 (by decide)).2.2.mpr rfl
  exact ⟨lt_of_le_of_ne h0.1 (by simpa using h0.2.2),
    lt_of_le_of_ne h1.1 (by simpa using h1.2.2), h2, h1.2.1⟩

end MathlibExtTest.NumberTheory.SpoofLehmerFactorizationSpoofLehmerLowerLeLeUpper
