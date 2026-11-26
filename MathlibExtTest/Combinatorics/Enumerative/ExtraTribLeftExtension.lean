/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import MathlibExt.Combinatorics.Enumerative.ExtraTribLeftExtension
import MathlibExt.NumberTheory.TribonacciInt

/-! # Tests for signs and difference-inverses of the two-sided Tribonacci sequence -/

namespace MetaMathlibExt.extraTrib_left_extension

private theorem tribonacciInt_isExtraTrib : IsExtraTrib tribonacciInt := by
  have hpos (m : ℕ) : 0 < tribonacci (m + 2) := by
    induction m with
    | zero => decide
    | succ m ih =>
      change 0 < tribonacci (m + 3)
      rw [tribonacci]
      omega
  refine ⟨tribonacciInt_add_three, 1, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Int.le.dest hn
  rw [Int.add_comm]
  change 0 < tribonacciInt ((m + 1 : ℕ) : ℤ)
  rw [tribonacciInt_nat_eq]
  exact_mod_cast hpos m

-- The triple immediately before the negative term at -3 ends in zero.
example : tribonacciInt (-4) = 0 ∧
    ¬ (0 < tribonacciInt (-6) ∧ 0 < tribonacciInt (-5) ∧ 0 < tribonacciInt (-4)) ∧
    ¬ (tribonacciInt (-6) < 0 ∧ tribonacciInt (-5) < 0 ∧ tribonacciInt (-4) < 0) :=
  ⟨rfl, (extraTrib_left_extension _ tribonacciInt_isExtraTrib).2 (-3) (by decide) (-6)
    (by decide)⟩


-- At the negative EEOO start (-1), the unique rational inverse is one half.
example : (∃! Q : ℤ → ℚ, (∀ n, Q (n + 3) = Q (n + 2) + Q (n + 1) + Q n) ∧
    (∀ n, Q (n + 1) - Q n = tribonacciInt n) ∧ Q (-1) = 1 / 2) ∧
    (¬ ∃ R : ℤ → ℤ, IsExtraTrib R ∧ ∀ n, R (n + 1) - R n = tribonacciInt n) ∧
    ∀ n : ℤ, Even (tribonacciInt n) ↔ (n - (-1)) % 4 < 2 := by
  obtain ⟨⟨Q, ⟨hrec, hdiff⟩, huniq⟩, hinteger⟩ :=
    extraTrib_difference_inverse (S := tribonacciInt) (hS := tribonacciInt_isExtraTrib)
  have h₀ := hdiff (-1)
  have h₁ := hdiff 1
  have h₂ := hrec (-1)
  change Q 0 - Q (-1) = 0 at h₀
  change Q 2 - Q 1 = 1 at h₁
  change Q 2 = Q 1 + Q 0 + Q (-1) at h₂
  have hhalf : Q (-1) = 1 / 2 := by linarith only [h₀, h₁, h₂]
  have hno : ¬ ∃ R : ℤ → ℤ, IsExtraTrib R ∧ ∀ n, R (n + 1) - R n = tribonacciInt n := by
    rintro ⟨R, hR, hd⟩
    have h₀ := hd (-1)
    have h₁ := hd 1
    have h₂ := hR.1 (-1)
    change R 0 - R (-1) = 0 at h₀
    change R 2 - R 1 = 1 at h₁
    change R 2 = R 1 + R 0 + R (-1) at h₂
    omega
  have hrot : ∃ k : ℤ, ∀ n, Even (tribonacciInt n) ↔ (n - k) % 4 < 2 := by
    by_contra h
    exact hno (hinteger.mpr h)
  obtain ⟨k, hk⟩ := hrot
  have hk₀ := (hk (-1)).mp ⟨0, rfl⟩
  have hk₁ := (hk 0).mp ⟨0, rfl⟩
  refine ⟨⟨Q, ⟨hrec, hdiff, hhalf⟩, fun R hR => huniq R ⟨hR.1, hR.2.1⟩⟩, hno, ?_⟩
  intro n
  rw [hk n]
  omega

-- Doubling clears the obstruction, and the integer inverse takes value one at -1.
example : ∃ R : ℤ → ℤ, IsExtraTrib R ∧
    (∀ n, R (n + 1) - R n = 2 * tribonacciInt n) ∧ R (-1) = 1 := by
  let S (n : ℤ) := 2 * tribonacciInt n
  have hS : IsExtraTrib S := by
    obtain ⟨hrec, N, hN⟩ := tribonacciInt_isExtraTrib
    refine ⟨?_, N, ?_⟩
    · intro n
      simp only [S, hrec n, mul_add]
    · intro n hn
      have := hN n hn
      dsimp [S]
      omega
  obtain ⟨R, hR, hd⟩ := (extraTrib_difference_inverse S hS).2.mpr (by
    rintro ⟨k, hk⟩
    have he : Even (S (k + 2)) := ⟨tribonacciInt (k + 2), by simp [S, two_mul]⟩
    have := (hk (k + 2)).1 he
    omega)
  refine ⟨R, hR, hd, ?_⟩
  have h₀ := hd (-1)
  have h₁ := hd 1
  have h₂ := hR.1 (-1)
  change R 0 - R (-1) = 0 at h₀
  change R 2 - R 1 = 2 at h₁
  change R 2 = R 1 + R 0 + R (-1) at h₂
  omega

end MetaMathlibExt.extraTrib_left_extension
