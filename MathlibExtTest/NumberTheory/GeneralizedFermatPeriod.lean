/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFermatPeriod

/-! # Tests for the start of the period of generalized Fermat numbers -/

open MetaMathlibExt

-- Modulo 9, the odd exponent base gives residues 3, 0, 0, … .
example : IsLeast {m : ℕ | ∃ T, 0 < T ∧
    Function.Periodic (fun k => (2 ^ 3 ^ (m + k) + 1) % 9) T} 1 := by
  apply (isLeast_periodic_start_pow_pow_add_one_mod_sq (a := 2) (b := 3) (p := 3) (n₀ := 1)
    (by decide) (by decide) (by decide) (by decide) ?_).1 (by decide)
  intro n hn
  obtain rfl : n = 0 := by omega
  decide

-- For the smallest prime and a first hit at index zero, the residues modulo 4 are 0, 2, 2, … .
example : IsLeast {m : ℕ | ∃ T, 0 < T ∧
    Function.Periodic (fun k => (3 ^ 2 ^ (m + k) + 1) % 4) T} 1 :=
  (isLeast_periodic_start_pow_pow_add_one_mod_sq (a := 3) (b := 2) (p := 2) (n₀ := 0)
    (by decide) (by decide) (by decide) (by decide) (by omega)).2 even_two

-- Modulo 25 the residues begin 8, 0, 2, so even the tail starting at the first zero is aperiodic.
example (T : ℕ) (hT : 0 < T) :
    ¬ Function.Periodic (fun k : ℕ => (7 ^ 2 ^ (1 + k) + 1) % 25) T := by
  have hmin (n : ℕ) (hn : n < 1) : ¬ 5 ^ 2 ∣ 7 ^ 2 ^ n + 1 := by
    obtain rfl : n = 0 := by omega
    decide
  have h := (isLeast_periodic_start_pow_pow_add_one_mod_sq (a := 7) (b := 2) (p := 5)
    (n₀ := 1) (by decide) (by decide) (by decide) (by decide) hmin).2 even_two
  intro hper
  exact Nat.not_succ_le_self 1 (h.2 ⟨T, hT, hper⟩)
