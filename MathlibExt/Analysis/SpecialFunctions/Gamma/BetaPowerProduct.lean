/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The beta integral for equal natural powers -/

@[expose] public section

/-- **Integral of $x^r (1-x)^r$ over $[0,1]$.** The integral is the reciprocal of
$(2r+1)\binom{2r}{r}$, including when $r=0$.

Source: Peiran Ding, Yanjun Zhu and Lei Wang, *A New Formula for the Sum of Integer Powers
Based on Elementary Matrix Theory*, Lemma 3, for positive integers $r$; for $r = 0$ the
integrand is constant and both sides are $1$. -/
theorem intervalIntegral.integral_pow_one_sub_pow (r : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ r * (1 - x) ^ r) =
      1 / ((2 * r + 1 : ℝ) * (Nat.choose (2 * r) r : ℝ)) := by
  have hβ : ((∫ x in (0 : ℝ)..1, x ^ r * (1 - x) ^ r : ℝ) : ℂ) =
      Complex.betaIntegral ((r : ℂ) + 1) ((r : ℂ) + 1) := by
    simpa only [Complex.betaIntegral, add_sub_cancel_right, Complex.cpow_natCast,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one] using
      (intervalIntegral.integral_ofReal (a := 0) (b := 1) (μ := MeasureTheory.volume)
        (f := fun x : ℝ => x ^ r * (1 - x) ^ r)).symm
  have hp : 0 < ((r : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  have hsum : ((r : ℂ) + 1) + ((r : ℂ) + 1) = ((2 * r + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hp hp, hsum] at hβ
  simp only [Complex.Gamma_nat_eq_factorial] at hβ
  have hfac : ((2 * r).choose r : ℝ) * (r.factorial : ℝ) * r.factorial =
      ((2 * r).factorial : ℝ) := by
    exact_mod_cast (show (2 * r).choose r * r.factorial * r.factorial = (2 * r).factorial by
      simpa only [two_mul] using Nat.add_choose_mul_factorial_mul_factorial r r)
  have hchoose : ((2 * r).choose r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show r ≤ 2 * r by omega)).ne'
  have hden : (2 * (r : ℝ) + 1) ≠ 0 := by positivity
  have hr : (r.factorial : ℝ) ≠ 0 := by positivity
  have hcalc : (r.factorial : ℝ) * r.factorial / ((2 * r + 1).factorial : ℝ) =
      1 / ((2 * r + 1 : ℝ) * ((2 * r).choose r : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Nat.cast_mul, Nat.cast_ofNat, ← hfac]
    field_simp [hchoose, hden, hr]
  apply Complex.ofReal_injective
  calc
    _ = (r.factorial : ℂ) * r.factorial / ((2 * r + 1).factorial : ℂ) := hβ
    _ = _ := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_div] using
        congrArg Complex.ofReal hcalc
