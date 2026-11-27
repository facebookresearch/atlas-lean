/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Padics.ShortRunValuationDensity
import Mathlib.Analysis.Complex.ExponentialBounds

namespace MetaMathlibExt.max_padicValNat_add_le_density_one

open Finset Real

private def startingPoints : Set ℕ :=
  {m | ∀ k : ℕ, log m / 2 < k → (k : ℝ) < log m → ∀ p : ℕ, p.Prime → p ≤ 2 * k →
    (((Icc 1 k).sup fun i => padicValNat p (m + i) : ℕ) : ℝ) ≤ 3 * log k / log p}

-- The same density-one set bounds the valuation at each individual shift.
example : ∃ S : Set ℕ, S.HasDensity 1 ∧ ∀ m ∈ S, ∀ k : ℕ, log m / 2 < k →
    (k : ℝ) < log m → ∀ p : ℕ, p.Prime → p ≤ 2 * k → ∀ i ∈ Icc 1 k,
      (padicValNat p (m + i) : ℝ) ≤ 3 * log k / log p := by
  refine ⟨startingPoints, max_padicValNat_add_le_density_one, ?_⟩
  intro m hm k hlo hhi p hp hpk i hi
  exact (Nat.cast_le.mpr (le_sup (f := fun j => padicValNat p (m + j)) hi)).trans
    (hm k hlo hhi p hp hpk)

-- For m = 3 the run k = 1 admits the endpoint prime p = 2k.
-- Its shift gives v₂(4) = 2, whereas log 1 = 0.
example : 3 ∉ startingPoints := by
  intro h
  have hlo : log 3 / 2 < 1 := by linarith [log_three_lt_d9]
  have hhi : 1 < log 3 := by linarith [log_three_gt_d9]
  have hbound := h 1 (by simpa using hlo) (by simpa using hhi) 2 Nat.prime_two (by decide)
  have hval : padicValNat 2 (3 + 1) = 2 := by decide +kernel
  norm_num [hval] at hbound

end MetaMathlibExt.max_padicValNat_add_le_density_one
