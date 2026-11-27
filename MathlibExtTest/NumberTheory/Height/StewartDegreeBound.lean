/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.StewartDegreeBound
public import Mathlib.NumberTheory.Real.Irrational

/-! # Tests for `MathlibExt.NumberTheory.Height.StewartDegreeBound` -/

@[expose] public section

namespace StewartDegreeBoundTest

open Polynomial NumberField MathlibExt.NumberTheory.AsymptoticDobrowolski

/-- `√2`, viewed in `ℂ`, is integral over `ℚ`: it is a root of `X ^ 2 - 2`. -/
theorem sqrt_two_isIntegral : IsIntegral ℚ ((Real.sqrt 2 : ℝ) : ℂ) := by
  refine ⟨X ^ 2 - C 2, monic_X_pow_sub_C 2 two_ne_zero, ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, ← Complex.ofReal_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp

/-- The minimal polynomial of `√2` over `ℚ` has degree `2`: it divides `X ^ 2 - 2`, and degree
`1` would make `√2` rational. -/
theorem sqrt_two_minpoly_natDegree : (minpoly ℚ ((Real.sqrt 2 : ℝ) : ℂ)).natDegree = 2 := by
  have hint := sqrt_two_isIntegral
  have hroot : aeval ((Real.sqrt 2 : ℝ) : ℂ) (X ^ 2 - C (2 : ℚ)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have hle : (minpoly ℚ ((Real.sqrt 2 : ℝ) : ℂ)).natDegree ≤ 2 := by
    have h := natDegree_le_of_dvd (minpoly.dvd ℚ _ hroot)
      (monic_X_pow_sub_C (2 : ℚ) two_ne_zero).ne_zero
    rwa [natDegree_X_pow_sub_C] at h
  have hne : (minpoly ℚ ((Real.sqrt 2 : ℝ) : ℂ)).natDegree ≠ 1 := by
    rw [Ne, minpoly.natDegree_eq_one_iff]
    rintro ⟨q, hq⟩
    apply irrational_sqrt_two.ne_rat q
    have hq' : ((q : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := by
      rw [← hq, Complex.ofReal_ratCast]
      rfl
    exact (Complex.ofReal_injective hq').symm
  have hpos := minpoly.natDegree_pos hint
  omega

/-- `√2` is not a root of unity, since its absolute value exceeds `1`. -/
theorem sqrt_two_not_isOfFinOrder : ¬IsOfFinOrder ((Real.sqrt 2 : ℝ) : ℂ) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, h⟩
  have hnorm := congrArg norm h
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2), norm_one] at hnorm
  exact (one_lt_pow₀ Real.one_lt_sqrt_two hn.ne').ne' hnorm

/-- A concrete witness: `√2` satisfies all the hypotheses (so they are not jointly vacuous), and
Stewart's bound gives `M(√2) > 1 + 1 / (20000 log 2)`. (In fact `M(√2) = 2`.) -/
theorem sqrt_two_stewart :
    1 + 1 / (10000 * 2 * Real.log 2) < algebraicMahlerMeasure ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h := stewart_degreeBound ((Real.sqrt 2 : ℝ) : ℂ)
    sqrt_two_isIntegral.isAlgebraic (by simp) sqrt_two_not_isOfFinOrder
    sqrt_two_minpoly_natDegree.ge
  rw [sqrt_two_minpoly_natDegree] at h
  exact_mod_cast h

/-- The bound forces the Mahler measure strictly above `1`. The hypotheses are passed by name,
as callers of the theorem do. -/
theorem one_lt_algebraicMahlerMeasure (α : ℂ) (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0)
    (hroot : ¬IsOfFinOrder α) (hd : 2 ≤ (minpoly ℚ α).natDegree) :
    1 < algebraicMahlerMeasure α := by
  have h := stewart_degreeBound α (hα := hα) (hα0 := hα0) (hroot := hroot) (hd := hd)
  have hdR : (2 : ℝ) ≤ (minpoly ℚ α).natDegree := by exact_mod_cast hd
  have hlog : 0 < Real.log (minpoly ℚ α).natDegree := Real.log_pos (by linarith)
  have hpos : 0 < 1 / (10000 * ((minpoly ℚ α).natDegree : ℝ) *
      Real.log (minpoly ℚ α).natDegree) := by positivity
  linarith

end StewartDegreeBoundTest
