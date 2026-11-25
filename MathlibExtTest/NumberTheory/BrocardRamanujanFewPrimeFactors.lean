/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BrocardRamanujanFewPrimeFactors
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.Simproc.Factors

open Nat MetaMathlibExt

-- `(4, 5)` is counted at `l = 2` through `x - 1 = 4 = 2 ^ 2`, although `x + 1 = 6` has two prime
-- factors, so the set of the theorem is not empty.
example : (4, 5) ∈ {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
    ((p.2 - 1).primeFactors.card < 2 ∨ (p.2 + 1).primeFactors.card < 2)} := by
  refine ⟨by decide, Or.inl ?_⟩
  norm_num [Nat.primeFactors]

-- The bound on the number of prime factors is strict: `(5, 11)` is a solution, but `10 = 2 * 5`
-- and `12 = 2 ^ 2 * 3` both have two prime factors, so it is excluded at `l = 2` and counted at
-- `l = 3`.
example : (5, 11) ∉ {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
    ((p.2 - 1).primeFactors.card < 2 ∨ (p.2 + 1).primeFactors.card < 2)} := by
  rintro ⟨-, h | h⟩ <;> norm_num [Nat.primeFactors] at h

example : (5, 11) ∈ {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
    ((p.2 - 1).primeFactors.card < 3 ∨ (p.2 + 1).primeFactors.card < 3)} := by
  refine ⟨by decide, Or.inl ?_⟩
  norm_num [Nat.primeFactors]

-- `(7, 71)` is counted at `l = 3` only through `x + 1 = 72 = 2 ^ 3 * 3 ^ 2`, since
-- `x - 1 = 70 = 2 * 5 * 7` has three prime factors.
example : (7, 71) ∈ {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
    ((p.2 - 1).primeFactors.card < 3 ∨ (p.2 + 1).primeFactors.card < 3)} := by
  refine ⟨by decide, Or.inr ?_⟩
  norm_num [Nat.primeFactors]

example : ¬(71 - 1 : ℕ).primeFactors.card < 3 := by
  norm_num [Nat.primeFactors]

-- A prime power has exactly one prime factor, so the case `l = 2` gives finitely many solutions
-- with `x - 1` or `x + 1` a prime power.
example : {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
    (IsPrimePow (p.2 - 1) ∨ IsPrimePow (p.2 + 1))}.Finite :=
  (brocardRamanujan_fewPrimeFactors_finite 2 le_rfl).subset fun _ ⟨h, hp⟩ =>
    ⟨h, hp.imp (fun h => by simp [isPrimePow_iff_card_primeFactors_eq_one.1 h])
      (fun h => by simp [isPrimePow_iff_card_primeFactors_eq_one.1 h])⟩

-- For each `l`, the factorial index `n` of the solutions is bounded.
example (l : ℕ) (hl : 2 ≤ l) : ∃ N, ∀ n x : ℕ, n ! + 1 = x ^ 2 →
    ((x - 1).primeFactors.card < l ∨ (x + 1).primeFactors.card < l) → n ≤ N := by
  obtain ⟨N, hN⟩ := ((brocardRamanujan_fewPrimeFactors_finite l hl).image Prod.fst).bddAbove
  exact ⟨N, fun n x hsol hfew => hN ⟨(n, x), ⟨hsol, hfew⟩, rfl⟩⟩
