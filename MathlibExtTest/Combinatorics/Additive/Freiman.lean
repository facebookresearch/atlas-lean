/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.Freiman
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped Pointwise
open MathlibExt.Combinatorics.Additive.FreimanBSGWanted

-- The set `{0, 1, 2}` has `|A + A| = 5 ≤ 2|A|`, so the constants of Freiman's theorem for `C = 2`
-- give a progression containing it of size at most `3K`.
example : ∃ (d₀ : ℕ) (K : ℝ), ∃ (d : ℕ) (x₀ : ℤ) (x : Fin d → ℤ) (k : Fin d → ℕ),
    d ≤ d₀ ∧ (∀ i, 0 < x i) ∧ ((∏ i, k i : ℕ) : ℝ) ≤ K * 3 ∧
      ∀ a ∈ ({0, 1, 2} : Finset ℤ), ∃ c : Fin d → ℕ, (∀ i, c i < k i) ∧
        a = x₀ + ∑ i, (c i : ℤ) * x i := by
  obtain ⟨d₀, K, h⟩ := freiman 2
  have hsum : (({0, 1, 2} : Finset ℤ) + {0, 1, 2}).card = 5 := by decide
  have hcard : ({0, 1, 2} : Finset ℤ).card = 3 := by decide
  obtain ⟨d, x₀, x, k, hd, hx, -, hprod, hmem⟩ :=
    h {0, 1, 2} (by simp) (by rw [hsum, hcard]; norm_num)
  exact ⟨d₀, K, d, x₀, x, k, hd, hx, by simpa [hcard] using hprod, hmem⟩

-- Uniformity: a single dimension bound `d₀` and a single constant `K` serve every interval
-- `{0, 1, …, n}`, since each has doubling at most `2`.
example : ∃ (d₀ : ℕ) (K : ℝ), ∀ n : ℕ, ∃ (d : ℕ) (x₀ : ℤ) (x : Fin d → ℤ) (k : Fin d → ℕ),
    d ≤ d₀ ∧ ((∏ i, k i : ℕ) : ℝ) ≤ K * (n + 1) ∧
      ∀ a ∈ Finset.Icc (0 : ℤ) n, ∃ c : Fin d → ℕ, (∀ i, c i < k i) ∧
        a = x₀ + ∑ i, (c i : ℤ) * x i := by
  obtain ⟨d₀, K, h⟩ := freiman 2
  refine ⟨d₀, K, fun n => ?_⟩
  have hcard : (Finset.Icc (0 : ℤ) n).card = n + 1 := by simp
  have hsub : Finset.Icc (0 : ℤ) n + Finset.Icc (0 : ℤ) n ⊆ Finset.Icc (0 : ℤ) (2 * n) := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    simp only [Finset.mem_Icc] at ha hb ⊢
    omega
  have hle : ((Finset.Icc (0 : ℤ) n + Finset.Icc (0 : ℤ) n).card : ℝ) ≤
      2 * (Finset.Icc (0 : ℤ) n).card := by
    have h1 := Finset.card_le_card hsub
    have h2 : (Finset.Icc (0 : ℤ) (2 * n)).card = 2 * n + 1 := by
      rw [Int.card_Icc]
      omega
    rw [hcard]
    have : (Finset.Icc (0 : ℤ) n + Finset.Icc (0 : ℤ) n).card ≤ 2 * (n + 1) := by omega
    exact_mod_cast this
  obtain ⟨d, x₀, x, k, hd, -, -, hprod, hmem⟩ := h _ (by simp) hle
  refine ⟨d, x₀, x, k, hd, ?_, hmem⟩
  rw [hcard] at hprod
  exact_mod_cast hprod
