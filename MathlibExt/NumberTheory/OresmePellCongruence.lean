/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring

/-! # Oresme–Pell congruence -/

namespace MetaMathlibExt

/-- **Oresme–Pell congruence modulo 49.** For every natural number $n$, the Pell numbers $P_n$
satisfy $2^n (5 P_{n+1} - 4 P_n) \equiv 7n + 5 \pmod{49}$ as integers.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 5.3 (`fq-2024-cookbacon061124-cor-5.3`). -/
public theorem two_pow_mul_pellNumber_combination_modEq (n : ℕ) :
    2 ^ n * (5 * (pellNumber (n + 1) : ℤ) - 4 * pellNumber n) ≡ 7 * n + 5 [ZMOD 49] := by
  let S (k : ℕ) : ℤ := 2 ^ k * (5 * (pellNumber (k + 1) : ℤ) - 4 * pellNumber k)
  let L (k : ℕ) : ℤ := 7 * k + 5
  change S n ≡ L n [ZMOD 49]
  have hP (k : ℕ) : (pellNumber (k + 2) : ℤ) = 2 * (pellNumber (k + 1) : ℤ) + pellNumber k := by
    rw [pellNumber.eq_3, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hS (k : ℕ) : S (k + 2) = 4 * S (k + 1) + 4 * S k := by
    dsimp only [S]
    rw [hP (k + 1), hP k, pow_succ (2 : ℤ) (k + 1), pow_succ (2 : ℤ) k]
    ring
  have hL (k : ℕ) : 4 * L (k + 1) + 4 * L k ≡ L (k + 2) [ZMOD 49] := by
    refine Int.modEq_iff_dvd.mpr ⟨-((k : ℤ) + 1), ?_⟩
    simp only [L, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  have h (k : ℕ) : (S k ≡ L k [ZMOD 49]) ∧ (S (k + 1) ≡ L (k + 1) [ZMOD 49]) := by
    induction k with
    | zero => exact ⟨by decide, by decide⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [hS k]
      exact ((ih.2.mul_left 4).add (ih.1.mul_left 4)).trans (hL k)
  exact (h n).1

end MetaMathlibExt
