/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.LeadLagCompensator

/-! Concrete lead, lag, and degenerate frequency responses. -/

open scoped Real
open MetaMathlibExt

example :
    let φ := fun ω : ℝ ↦ (((1 : ℂ) + (ω : ℂ) * Complex.I) /
      ((4 : ℂ) + (ω : ℂ) * Complex.I)).arg
    0 < φ 1 ∧ φ 1 < φ 2 ∧ Real.sin (φ 2) = 3 / 5 ∧ Real.tan (φ 2) = 3 / 4 := by
  intro φ
  obtain ⟨_, _, _, hsin, htan, hlead, _⟩ :=
    lead_lag_frequency_response (k := 1) (a := 1) (b := 4)
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hsign, _, _, hmax⟩ := hlead (by norm_num)
  have hr : √((1 : ℝ) * 4) = 2 := by
    rw [one_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  dsimp only at hmax hsin htan
  rw [hr] at hmax hsin htan
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [φ] using hsign 1 (by norm_num)
  · simpa [φ] using hmax 1 (by norm_num) (by norm_num)
  · norm_num [φ] at hsin ⊢
    exact hsin
  · norm_num [φ] at htan ⊢
    exact htan

example :
    let φ := fun ω : ℝ ↦ (((4 : ℂ) + (ω : ℂ) * Complex.I) /
      ((1 : ℂ) + (ω : ℂ) * Complex.I)).arg
    φ 1 < 0 ∧ φ 2 < φ 3 ∧ Real.sin (φ 2) = -(3 / 5) ∧ Real.tan (φ 2) = -(3 / 4) := by
  intro φ
  obtain ⟨_, _, _, hsin, htan, _, hlag⟩ :=
    lead_lag_frequency_response (k := 1) (a := 4) (b := 1)
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hsign, _, _, hmin⟩ := hlag (by norm_num)
  have hr : √((4 : ℝ) * 1) = 2 := by
    rw [mul_one, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  dsimp only at hmin hsin htan
  rw [hr] at hmin hsin htan
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [φ] using hsign 1 (by norm_num)
  · simpa [φ] using hmin 3 (by norm_num) (by norm_num)
  · norm_num [φ] at hsin ⊢
    exact hsin
  · norm_num [φ] at htan ⊢
    exact htan

example {k a : ℝ} (hk : 0 < k) (ha : 0 < a) (ω : ℝ) :
    (((k : ℂ) * ((a : ℂ) + (ω : ℂ) * Complex.I)) /
      ((a : ℂ) + (ω : ℂ) * Complex.I)).arg = 0 := by
  simpa using ((lead_lag_frequency_response hk ha ha).1 ω).2.1

example {k a b : ℝ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) :
    ‖(k : ℂ) * (a : ℂ) / (b : ℂ)‖ = k * a / b ∧
      ((k : ℂ) * (a : ℂ) / (b : ℂ)).arg = 0 := by
  have h := lead_lag_frequency_response hk ha hb
  exact ⟨by simpa using h.2.1, by simpa using (h.1 0).2.1⟩
