/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MonochromaticSumsLinearErdosProblem484
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Tests for `MathlibExt.Combinatorics.MonochromaticSumsLinearErdosProblem484` -/

namespace MathlibExtTest.MonochromaticSumsLinearErdosProblem484

open MathlibExt.Combinatorics.MonochromaticSumsLinearErdosProblem484Wanted

/-- The colouring of `ℕ` by parity. -/
private def parity (n : ℕ) : Fin 2 := if n % 2 = 0 then 0 else 1

/-- Two numbers of the same parity colour have the same parity. -/
private theorem mod_two_eq_of_parity_eq {a b : ℕ} (h : parity a = parity b) :
    a % 2 = b % 2 := by
  unfold parity at h
  split_ifs at h <;> omega

-- Test section: small cases of the counted set.

-- With one colour, the monochromatic sums in `{1, …, 5}` are `3`, `4` and `5`; `2 = 1 + 1` does
-- not count, since the two summands must be distinct.
example : {n : ℕ | n ∈ Finset.Icc 1 5 ∧ ∃ a ∈ Finset.Icc 1 5, ∃ b ∈ Finset.Icc 1 5,
    a ≠ b ∧ (fun _ => (0 : Fin 1)) a = (fun _ => (0 : Fin 1)) b ∧ a + b = n}.ncard = 3 := by
  rw [Set.ncard_eq_three]
  refine ⟨3, 4, 5, by decide, by decide, by decide, Set.ext fun n => ⟨?_, ?_⟩⟩
  · rintro ⟨hn, a, ha, b, hb, hab, -, rfl⟩
    simp only [Finset.mem_Icc] at hn ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨by simp, 1, by simp, 2, by simp, by decide, rfl, rfl⟩
    · exact ⟨by simp, 1, by simp, 3, by simp, by decide, rfl, rfl⟩
    · exact ⟨by simp, 1, by simp, 4, by simp, by decide, rfl, rfl⟩

-- Under the parity colouring, the monochromatic sums in `{1, …, 6}` are `4 = 1 + 3` and
-- `6 = 1 + 5 = 2 + 4`.
example : {n : ℕ | n ∈ Finset.Icc 1 6 ∧ ∃ a ∈ Finset.Icc 1 6, ∃ b ∈ Finset.Icc 1 6,
    a ≠ b ∧ parity a = parity b ∧ a + b = n}.ncard = 2 := by
  rw [Set.ncard_eq_two]
  refine ⟨4, 6, by decide, Set.ext fun n => ⟨?_, ?_⟩⟩
  · rintro ⟨hn, a, ha, b, hb, hab, hf, rfl⟩
    have := mod_two_eq_of_parity_eq hf
    simp only [Finset.mem_Icc] at hn ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rintro (rfl | rfl)
    · exact ⟨by simp, 1, by simp, 3, by simp, by decide, rfl, rfl⟩
    · exact ⟨by simp, 2, by simp, 4, by simp, by decide, rfl, rfl⟩

-- Test section: the constant. Under the parity colouring no odd number is a monochromatic sum,
-- so a constant `c` as in the statement is at most `1 / 2`.
example (N n : ℕ) (hn : Odd n) : n ∉ {n : ℕ | n ∈ Finset.Icc 1 N ∧
    ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, a ≠ b ∧ parity a = parity b ∧ a + b = n} := by
  rintro ⟨-, a, -, b, -, -, hf, rfl⟩
  have := mod_two_eq_of_parity_eq hf
  rw [Nat.odd_iff] at hn
  omega

-- Test section: the theorem. For a fixed number of colours, the number of monochromatic sums in
-- `{1, …, N}` tends to infinity with `N`, uniformly in the colouring.
example (k : ℕ) (hk : 0 < k) (B : ℕ) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : ℕ → Fin k,
    B ≤ {n : ℕ | n ∈ Finset.Icc 1 N ∧
      ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, a ≠ b ∧ f a = f b ∧ a + b = n}.ncard := by
  obtain ⟨c, hc, h⟩ := monochromaticSumsLinearCount_holds
  obtain ⟨N₀, hN₀⟩ := h k hk
  refine ⟨max N₀ ⌈(B : ℝ) / c⌉₊, fun N hN f => ?_⟩
  have h1 := hN₀ N (le_of_max_le_left hN) f
  have h2 : (B : ℝ) / c ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hN)
  have h3 : (B : ℝ) ≤ c * N := by rwa [div_le_iff₀ hc, mul_comm] at h2
  exact_mod_cast h3.trans h1

end MathlibExtTest.MonochromaticSumsLinearErdosProblem484
