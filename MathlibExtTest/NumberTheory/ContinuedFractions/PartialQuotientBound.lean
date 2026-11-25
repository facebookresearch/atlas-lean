/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ContinuedFractions.PartialQuotientBound
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.Translations

namespace MetaMathlibExt

open GenContFract

-- Here q₀ = 1 and q₁ = 4. Apply the bound at N = 0 to 0/1 and the unreduced 0/2.
example : 1 / 6 < |(3 + Real.sqrt 2)⁻¹| ∧ 1 / 12 < |2 * (3 + Real.sqrt 2)⁻¹| := by
  let γ : ℝ := (3 + Real.sqrt 2)⁻¹
  change 1 / 6 < |γ| ∧ 1 / 12 < |2 * γ|
  have hγ : Irrational γ :=
    (by simpa using irrational_sqrt_two.natCast_add 3 : Irrational (3 + Real.sqrt 2)).inv
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h₁ : 1 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have h₂ : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hγpos : 0 < γ := inv_pos.mpr (by linarith)
  have hfloor : ⌊γ⌋ = 0 :=
    Int.floor_eq_iff.mpr (by simpa using ⟨hγpos.le, inv_lt_one_of_one_lt₀ (by linarith)⟩)
  have hfloor' : ⌊3 + Real.sqrt 2⌋ = 4 := Int.floor_eq_iff.mpr (by
    norm_num
    exact ⟨by linarith, by linarith⟩)
  have hfr : (IntFractPair.of γ).fr = γ := by simp [IntFractPair.of, Int.fract, hfloor]
  have hfr₀ : (IntFractPair.of γ).fr ≠ 0 := by rw [hfr]; exact hγpos.ne'
  have hstep := IntFractPair.stream_succ_of_some (IntFractPair.stream_zero γ) hfr₀
  rw [hfr, show γ⁻¹ = 3 + Real.sqrt 2 by simp [γ]] at hstep
  have hs : (GenContFract.of γ).s.get? 0 = some ⟨1, 4⟩ := by
    simpa [IntFractPair.of, hfloor'] using
      get?_of_eq_some_of_succ_get?_intFractPair_stream hstep
  have hq₀ : (GenContFract.of γ).dens 0 ≤ (3 : ℝ) := by norm_num [zeroth_den_eq_one]
  have hq₁ : (3 : ℝ) < (GenContFract.of γ).dens (0 + 1) := by norm_num [first_den_eq hs]
  have ha₀ : (⌊γ⌋ : ℝ) ≤ 4 := by norm_num [hfloor]
  have ha (j : ℕ) (hj : j ≤ 0) (b : ℝ)
      (hb : (GenContFract.of γ).partDens.get? j = some b) : b ≤ 4 := by
    have hj₀ : j = 0 := Nat.le_zero.mp hj
    have h : (4 : ℝ) = b := by simpa [hj₀, partDen_eq_s_b hs] using hb
    exact h.ge
  have lower (x : ℤ) := one_div_partialQuotient_bound_mul_lt_abs_mul_sub hγ
    (M := 3) (N := 0) (by decide) hq₀ hq₁ ha₀ ha (x := x) (y := 0)
  constructor
  · have h := lower 1 (by decide) (by decide)
    norm_num at h ⊢
    exact h
  · have h := lower 2 (by decide) (by decide)
    norm_num at h ⊢
    exact h

end MetaMathlibExt
