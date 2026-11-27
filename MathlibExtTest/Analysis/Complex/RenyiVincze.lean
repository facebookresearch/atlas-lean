/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.RenyiVincze
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Set MeasureTheory
open MathlibExt.Analysis.HaymanProblem232Wanted

-- Apply the refutation to recover the scale factor from the ratio condition alone.
example (f : ℂ → ℂ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hinf : ∀ N, ∃ n ≥ N, a n ≠ 0)
    (hs : ∀ z, HasSum (fun n => (a n : ℂ) * z ^ n) (f z))
    (hf : DifferentiableOn ℂ f univ)
    (hr : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∫ x : ℝ in Ici 0, f (↑(ρ * x)) / f x = 1 / (1 - (ρ : ℂ))) :
    ∃ c : ℝ, 0 < c ∧ f = fun z => (c : ℂ) * Complex.exp z := by
  by_contra! h
  exact conjecture_refuted ⟨f, a, h, ha, hinf, hs, hf, Or.inr hr⟩

-- A nonunit positive prefactor cancels from the ratio.
example (ρ : ℝ) (hρ : ρ < 1) :
    ∫ x : ℝ in Ici 0, (2 * Complex.exp (↑(ρ * x))) / (2 * Complex.exp x) =
      1 / (1 - (ρ : ℂ)) := by
  have he (x : ℝ) : (2 * Complex.exp (↑(ρ * x))) / (2 * Complex.exp x) =
      Complex.exp (((ρ : ℂ) - 1) * x) := by
    rw [mul_div_mul_left _ _ (two_ne_zero : (2 : ℂ) ≠ 0), ← Complex.exp_sub,
      Complex.ofReal_mul, sub_mul, one_mul]
  simp_rw [he, integral_Ici_eq_integral_Ioi]
  rw [integral_exp_mul_complex_Ioi (a := (ρ : ℂ) - 1) (by simpa using sub_neg.mpr hρ)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [← neg_sub (1 : ℂ) (ρ : ℂ), neg_div_neg_eq]
