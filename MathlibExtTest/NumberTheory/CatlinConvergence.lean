/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CatlinConvergence

/-!
# Tests for the convergent case of Catlin's conjecture
-/

open Set MeasureTheory NNReal ENNReal

namespace MathlibExt.NumberTheory.DuffinSchaefferConjectureWanted.DuffinSchaefferConjecture.Tests

private theorem zero_star (q : ℕ+) : ψ_star (fun _ ↦ 0) q = 0 := by
  have h : sSup {r : ℝ≥0∞ | ∃ n : ℕ+, q ∣ n ∧ r = (0 : ℝ≥0) / n} = 0 := by
    refine le_antisymm (sSup_le ?_) bot_le
    rintro r ⟨n, _, rfl⟩
    simp
  simp only [ψ_star, h, mul_zero]

-- Even at zero radius, the pairs (q, q) give infinitely many exact approximations to 1.
example : (1 : ℝ) ∈ 𝒦 (fun _ ↦ 0) := by
  refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
  let f (q : ℕ+) : ℕ × ℕ+ := (q, q)
  have h : Function.Injective f := fun _ _ he ↦ congrArg Prod.snd he
  refine (infinite_range_of_injective h).mono ?_
  rintro _ ⟨q, rfl⟩
  have hq : (q : ℝ) ≠ 0 := by positivity
  simp [f, inequality_1_7, hq]

example : MeasurableSet (𝒦 (fun _ ↦ 0)) ∧ volume (𝒦 (fun _ ↦ 0)) = 0 := by
  apply theorem_2_a
  simp [zero_star]

-- A positive radius supported at 6 contributes to the supremum for reduced denominator 3.
example : 2 ≤ ψ_star (fun q ↦ if q = 6 then 6 else 0) 3 := by
  have h : (1 : ℝ≥0∞) ≤
      sSup {r : ℝ≥0∞ | ∃ n : ℕ+, (3 : ℕ+) ∣ n ∧
        r = ((if n = 6 then 6 else 0 : ℝ≥0) : ℝ≥0∞) / n} := by
    apply le_sSup
    refine ⟨6, ⟨2, rfl⟩, ?_⟩
    norm_num [ENNReal.div_self (by norm_num : (6 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top]
  change 2 ≤ (Nat.totient 3 : ℝ≥0∞) * _
  calc
    2 = (Nat.totient 3 : ℝ≥0∞) * 1 := by
      rw [Nat.totient_prime (by decide : Nat.Prime 3)]
      norm_num
    _ ≤ _ := by gcongr

end MathlibExt.NumberTheory.DuffinSchaefferConjectureWanted.DuffinSchaefferConjecture.Tests
