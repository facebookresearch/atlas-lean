/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.KFull
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

-- The powerful part handles the degenerate inputs and keeps only prime powers
-- with exponent at least two.
example : Nat.powerfulPart 0 = 1 := Nat.powerfulPart_zero
example : Nat.powerfulPart 1 = 1 := Nat.powerfulPart_one

-- Pointwise factorization API: exponents at least two are kept.
example (n p : ℕ) (h : 2 ≤ n.factorization p) :
    (Nat.powerfulPart n).factorization p = n.factorization p := by
  rw [Nat.powerfulPart_factorization, ite_eq_left h]

-- Pointwise factorization API: exponents below two are erased.
example (n p : ℕ) (h : n.factorization p < 2) :
    (Nat.powerfulPart n).factorization p = 0 := by
  rw [Nat.powerfulPart_factorization, ite_eq_right (by omega)]

-- Divisibility API.
example (n : ℕ) : Nat.powerfulPart n ∣ n := Nat.powerfulPart_dvd n
example : Nat.powerfulPart 36 ∣ 36 := Nat.powerfulPart_dvd 36

-- `1` is `k`-full, for the source case `k = 2` and generically.
example : Nat.IsKFull 2 1 := Nat.isKFull_one 2
example (k : ℕ) : Nat.IsKFull k 1 := Nat.isKFull_one k

-- `0` is never `k`-full.
example : ¬ Nat.IsKFull 2 0 := Nat.not_isKFull_zero 2
example (k : ℕ) : ¬ Nat.IsKFull k 0 := Nat.not_isKFull_zero k

-- Explicit `k = 0` extension, both directions.
example : Nat.IsKFull 0 5 := Nat.isKFull_k_eq_zero.mpr (by decide)
example (h : Nat.IsKFull 0 5) : (5 : ℕ) ≠ 0 := Nat.isKFull_k_eq_zero.mp h

-- Explicit `k = 1` extension, both directions.
example : Nat.IsKFull 1 7 := Nat.isKFull_k_eq_one.mpr (by decide)
example (h : Nat.IsKFull 1 7) : (7 : ℕ) ≠ 0 := Nat.isKFull_k_eq_one.mp h

-- Factorization characterization, used here to reprove a vacuous case.
example : Nat.IsKFull 3 1 :=
  (Nat.isKFull_iff_factorization one_ne_zero).mpr fun _p hp hpn =>
    absurd (Nat.dvd_one.mp hpn) hp.ne_one

-- Exponent monotonicity.
example : Nat.IsKFull 2 1 :=
  Nat.isKFull_mono (show 2 ≤ 3 by decide) (Nat.isKFull_one 3)

-- Source-facing `k ≥ 2` implication to `2`-full.
example : Nat.IsKFull 2 1 :=
  Nat.isKFull_of_two_le (show 2 ≤ 5 by decide) (Nat.isKFull_one 5)

-- `k = 2` squarefull/powerful specialization, both directions.
example (h : Nat.IsKFull 2 1) :
    (1 : ℕ) ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ 1 → p ^ 2 ∣ 1 :=
  Nat.isKFull_two.mp h
example : Nat.IsKFull 2 1 :=
  Nat.isKFull_two.mpr
    ⟨one_ne_zero, fun _p hp hpn => absurd (Nat.dvd_one.mp hpn) hp.ne_one⟩

-- Nontrivial positive case: `36 = 2 ^ 2 * 3 ^ 2` is `2`-full.
example : Nat.IsKFull 2 36 := by
  refine ⟨by decide, fun p hp hpn => ?_⟩
  have hle : p ≤ 36 := Nat.le_of_dvd (by decide) hpn
  have hp2 := hp.two_le
  interval_cases p <;> revert hp hpn hp2 hle <;> decide

-- Nontrivial negative cases: `12` is not `3`-full and `8` is not `4`-full.
example : ¬ Nat.IsKFull 3 12 := by
  intro h
  exact absurd (h.2 3 (by decide) (by decide)) (by decide)
example : ¬ Nat.IsKFull 4 8 := by
  intro h
  exact absurd (h.2 2 (by decide) (by decide)) (by decide)
