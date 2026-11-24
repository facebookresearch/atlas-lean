/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SpoofLehmerFactorization

/-!
# Tests for spoof Lehmer factorizations and the Lehmer function
-/

open MetaMathlibExt

-- A single factor with exponent two satisfies the Lehmer hypotheses for any integer multiplier.
example (k : ℤ) : IsSpoofLehmer k {(1, 2)} ∧ IsTrivialSpoof {(1, 2)} := by
  have hL : IsSpoofLehmer k {(1, 2)} := by
    refine ⟨?_, ?_, Or.inr ?_⟩ <;> simp [IsSpoofFactorization, spoofTotient, spoofEval]
  exact ⟨hL, isTrivialSpoof_of_isSpoofLehmer_of_one_mem _ ⟨k, hL⟩ (by simp)⟩

-- A base one rules out any second base greater than one.
example (k : ℤ) (x : ℕ) (hx : 1 < x) : ¬ IsSpoofLehmer k {(x, 1), (1, 1)} := by
  intro hL
  have h := isTrivialSpoof_of_isSpoofLehmer_of_one_mem _ ⟨k, hL⟩ (by simp)
  exact hx.ne' (h (x, 1) (by simp))

-- The upper endpoint is attained in every admissible length.
example (r : ℕ) : lehmerKappa (List.replicate r 2) = 2 ^ r - 1 := by
  norm_num [lehmerKappa, List.map_replicate, List.prod_replicate]

-- At length one, the strict lower bound fails throughout the domain.
example (x : ℝ) (hx : 2 ≤ x) : lehmerKappa [x] = 1 := by
  have h : x - 1 ≠ 0 := by linarith
  simp [lehmerKappa, h]

-- Increasing the middle entry of an unsorted list with repeated entries.
example (y : ℝ) (hy : 2 < y) : lehmerKappa [3, y, 2] < lehmerKappa [3, 2, 2] := by
  have h := lehmerKappa_antitone_bounds 3 (by decide) [3, 2, 2] rfl (by norm_num)
  exact h.2 1 (by decide) y hy
