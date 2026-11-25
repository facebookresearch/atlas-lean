/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.SquareSummableComplexInequality
import Mathlib.NumberTheory.ZetaValues

/-! # Tests for `MathlibExt.Analysis.Series.SquareSummableComplexInequality` -/

namespace MathlibExtTest.SquareSummableComplexInequality

open MathlibExt.Analysis.SquareSummableComplexInequalityWanted

-- Test section: the point mass at `1`, i.e. `α₁ = 1` and `αₙ = 0` for `n ≥ 2`. Since
-- `1 = 2 ^ 0 * (2 * 0 + 1)`, `β₀ = α₁ / 1 = 1` and `βₖ = 0` for `k ≥ 1`, so the inequality reads
-- `1 ≥ 6 / π ^ 2`.
example : 6 / Real.pi ^ 2 ≤ 1 := by
  let α : ℕ → ℂ := fun n => if n = 1 then 1 else 0
  have hα (n : ℕ) : ‖α (n + 1)‖ ^ 2 = if n = 0 then 1 else 0 := by
    by_cases hn : n = 0 <;> simp [α, hn]
  have hβ (k : ℕ) :
      ‖∑' l, α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ)‖ ^ 2 = if k = 0 then 1 else 0 := by
    have hterm (l : ℕ) : α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ) =
        if l = 0 then (if k = 0 then 1 else 0) else 0 := by
      by_cases hl : l = 0 <;> by_cases hk : k = 0 <;> simp [α, hl, hk]
    simp_rw [hterm, tsum_ite_eq]
    by_cases hk : k = 0 <;> simp [hk]
  have hsum : Summable fun n => ‖α (n + 1)‖ ^ 2 := by
    simp_rw [hα]
    exact (hasSum_ite_eq 0 1).summable
  have h := (conjecture_holds α hsum).2.2
  simp_rw [hα, hβ, tsum_ite_eq, mul_one] at h
  exact h

-- Test section: `αₙ = 1 / n`, a square-summable sequence with every `βₖ ≠ 0`. The theorem gives
-- the convergence of every `βₖ` and of `∑ₖ |βₖ|²`, and with `∑ₙ 1 / n ^ 2 = π ^ 2 / 6` it bounds
-- `∑ₖ |βₖ|²` by `(π ^ 2 / 6) ^ 2`.
example : (∀ k : ℕ, Summable fun l : ℕ => 1 / ((2 ^ k * (2 * l + 1) : ℕ) : ℂ) / (l + 1 : ℂ)) ∧
    Summable (fun k : ℕ => ‖∑' l : ℕ, 1 / ((2 ^ k * (2 * l + 1) : ℕ) : ℂ) / (l + 1 : ℂ)‖ ^ 2) ∧
    ∑' k : ℕ, ‖∑' l : ℕ, 1 / ((2 ^ k * (2 * l + 1) : ℕ) : ℂ) / (l + 1 : ℂ)‖ ^ 2 ≤
      (Real.pi ^ 2 / 6) ^ 2 := by
  have hα (n : ℕ) : ‖1 / ((n + 1 : ℕ) : ℂ)‖ ^ 2 = 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [norm_div, norm_one, Complex.norm_natCast, div_pow, one_pow]
  have hζ : HasSum (fun n : ℕ => ‖1 / ((n + 1 : ℕ) : ℂ)‖ ^ 2) (Real.pi ^ 2 / 6) := by
    simp_rw [hα]
    simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  obtain ⟨h₁, h₂, h₃⟩ := conjecture_holds (fun n => 1 / (n : ℂ)) hζ.summable
  refine ⟨h₁, h₂, ?_⟩
  rw [ge_iff_le, hζ.tsum_eq] at h₃
  calc _ = Real.pi ^ 2 / 6 * (6 / Real.pi ^ 2 *
        ∑' k : ℕ, ‖∑' l : ℕ, 1 / ((2 ^ k * (2 * l + 1) : ℕ) : ℂ) / (l + 1 : ℂ)‖ ^ 2) := by
        field_simp
    _ ≤ Real.pi ^ 2 / 6 * (Real.pi ^ 2 / 6) := by gcongr
    _ = (Real.pi ^ 2 / 6) ^ 2 := (sq _).symm

end MathlibExtTest.SquareSummableComplexInequality
