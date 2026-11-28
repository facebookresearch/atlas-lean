/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dirichlet series on a vertical line

On the line `re s = c` the terms `LSeries.term a (c + it) n` are continuous in `t` and have
modulus `‖LSeries.term a c n‖`, independent of `t`. Absolute convergence at `c` therefore
dominates the whole line, and a Dirichlet series can be integrated term by term against any
integrable kernel on the line.

## Main statements

* `LSeries.norm_term_vertical`, `LSeries.continuous_term_vertical`.
* `LSeriesSummable.continuous_vertical`, `LSeriesSummable.norm_vertical_le`: the series is
  continuous and bounded on the line.
* `LSeriesSummable.integrable_vertical_mul`: the series times an integrable kernel is
  integrable.
* `LSeriesSummable.hasSum_intervalIntegral_term_vertical_mul`: term-by-term integration over
  a finite segment against a bounded continuous kernel.
* `LSeriesSummable.hasSum_integral_term_vertical_mul`: term-by-term integration,
  `∑ₙ ∫ term a (c + it) n * K t dt = ∫ LSeries a (c + it) * K t dt`.
* `LSeriesSummable.hasSum_intervalIntegral_term_vertical_mul`: the same over a segment
  `[-R, R]` against a bounded continuous kernel.
* `LSeries.term_mul_cpow_div`: `term a s n · x^s / s = a n (x/n)^s / s`.
-/

@[expose] public section

open MeasureTheory Complex

namespace LSeries

/-- On a vertical line the terms of a Dirichlet series have constant modulus. -/
theorem norm_term_vertical (a : ℕ → ℂ) (c t : ℝ) (n : ℕ) :
    ‖term a (c + t * I) n‖ = ‖term a c n‖ := by
  rw [norm_term_eq, norm_term_eq]
  simp

/-- The terms of a Dirichlet series are continuous along a vertical line. -/
theorem continuous_term_vertical (a : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous fun t : ℝ => term a (c + t * I) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa only [term_zero] using continuous_const
  · simp only [term_of_ne_zero hn]
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    exact continuous_const.div (Continuous.const_cpow (by fun_prop) (Or.inl hn'))
      fun t h => hn' ((cpow_eq_zero_iff _ _).mp h).1

/-- A term of a Dirichlet series times an integrable kernel is integrable on a vertical
line. -/
theorem integrable_term_vertical_mul (a : ℕ → ℂ) (c : ℝ) {K : ℝ → ℂ} (hK : Integrable K)
    (n : ℕ) : Integrable fun t : ℝ => term a (c + t * I) n * K t :=
  hK.bdd_mul (continuous_term_vertical a c n).aestronglyMeasurable
    (ae_of_all _ fun t => (norm_term_vertical a c t n).le)

/-- `term a s n · x^s / s = a n · (x/n)^s / s` for `n ≠ 0` and `x > 0`. -/
theorem term_mul_cpow_div (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    term a s n * (x : ℂ) ^ s / s = a n * (((x / n : ℝ) : ℂ) ^ s / s) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hprod : ((x / n : ℝ) : ℂ) ^ s * ((n : ℝ) : ℂ) ^ s = (x : ℂ) ^ s := by
    rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) hnR.le]
    congr 2
    push_cast
    field_simp
  have hnne : ((n : ℝ) : ℂ) ^ s ≠ 0 := fun h =>
    (by exact_mod_cast hnR.ne' : ((n : ℝ) : ℂ) ≠ 0) ((Complex.cpow_eq_zero_iff _ _).mp h).1
  rw [term_of_ne_zero hn, ← hprod]
  push_cast at hnne ⊢
  field_simp

end LSeries

namespace LSeriesSummable

variable {a : ℕ → ℂ} {c : ℝ}

/-- Absolute convergence at `c` gives absolute convergence at every point of the line
`re s = c`. -/
theorem vertical (h : LSeriesSummable a c) (t : ℝ) : LSeriesSummable a (c + t * I) :=
  h.of_re_le_re (by simp)

/-- Absolute convergence at `c` gives absolute convergence on the whole line `re s = c`. -/
theorem summable_norm_term_vertical (h : LSeriesSummable a c) (t : ℝ) :
    Summable fun n => ‖LSeries.term a (c + t * I) n‖ := by
  simpa only [LSeries.norm_term_vertical] using summable_norm_iff.mpr h

/-- An absolutely convergent Dirichlet series is continuous along the line `re s = c`. -/
theorem continuous_vertical (h : LSeriesSummable a c) :
    Continuous fun t : ℝ => LSeries a (c + t * I) :=
  continuous_tsum (LSeries.continuous_term_vertical a c) (summable_norm_iff.mpr h)
    fun n t => (LSeries.norm_term_vertical a c t n).le

/-- An absolutely convergent Dirichlet series is bounded on the line `re s = c`. -/
theorem norm_vertical_le (h : LSeriesSummable a c) (t : ℝ) :
    ‖LSeries a (c + t * I)‖ ≤ ∑' n, ‖LSeries.term a c n‖ := by
  refine (norm_tsum_le_tsum_norm (h.summable_norm_term_vertical t)).trans_eq ?_
  simp only [LSeries.norm_term_vertical]

/-- **Term-by-term integration over a finite segment.** If `LSeriesSummable a c` and `K` is
continuous and bounded, then
`∑ₙ ∫_{-R}^R term a (c + it) n * K t dt = ∫_{-R}^R LSeries a (c + it) * K t dt`. -/
theorem hasSum_intervalIntegral_term_vertical_mul (h : LSeriesSummable a c) {K : ℝ → ℂ}
    (hK : Continuous K) {B : ℝ} (hKB : ∀ t, ‖K t‖ ≤ B) (R : ℝ) :
    HasSum (fun n => ∫ t in (-R)..R, LSeries.term a (c + t * I) n * K t)
      (∫ t in (-R)..R, LSeries a (c + t * I) * K t) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n _ => ‖LSeries.term a c n‖ * B) ?_ ?_ ?_ ?_ ?_
  · intro n
    exact ((LSeries.continuous_term_vertical a c n).mul hK).aestronglyMeasurable
  · intro n
    filter_upwards with t _
    rw [norm_mul, LSeries.norm_term_vertical]
    exact mul_le_mul_of_nonneg_left (hKB t) (norm_nonneg _)
  · filter_upwards with t _
    exact (summable_norm_iff.mpr h).mul_right _
  · exact intervalIntegrable_const
  · filter_upwards with t _
    exact (h.vertical t).LSeriesHasSum.mul_right (K t)

/-- An absolutely convergent Dirichlet series times an integrable kernel is integrable on the
line `re s = c`. -/
theorem integrable_vertical_mul (h : LSeriesSummable a c) {K : ℝ → ℂ} (hK : Integrable K) :
    Integrable fun t : ℝ => LSeries a (c + t * I) * K t :=
  hK.bdd_mul h.continuous_vertical.aestronglyMeasurable (ae_of_all _ fun t => h.norm_vertical_le t)

/-- **Term-by-term integration on a vertical line.** If `LSeriesSummable a c` and `K` is
integrable, then `∑ₙ ∫ term a (c + it) n * K t dt = ∫ LSeries a (c + it) * K t dt`. -/
theorem hasSum_integral_term_vertical_mul (h : LSeriesSummable a c) {K : ℝ → ℂ}
    (hK : Integrable K) :
    HasSum (fun n => ∫ t : ℝ, LSeries.term a (c + t * I) n * K t)
      (∫ t : ℝ, LSeries a (c + t * I) * K t) := by
  have hnorm : ∀ n : ℕ, ∫ t : ℝ, ‖LSeries.term a (c + t * I) n * K t‖ =
      ‖LSeries.term a c n‖ * ∫ t : ℝ, ‖K t‖ := by
    intro n
    simp only [norm_mul, LSeries.norm_term_vertical]
    exact integral_const_mul _ _
  have hsum : Summable fun n : ℕ => ∫ t : ℝ, ‖LSeries.term a (c + t * I) n * K t‖ := by
    simp only [hnorm]
    exact (summable_norm_iff.mpr h).mul_right _
  have hHS := hasSum_integral_of_summable_integral_norm
    (LSeries.integrable_term_vertical_mul a c hK) hsum
  have hfun : (fun t : ℝ => ∑' n, LSeries.term a (c + t * I) n * K t) =
      fun t : ℝ => LSeries a (c + t * I) * K t :=
    funext fun t => by rw [tsum_mul_right]; rfl
  rwa [hfun] at hHS

end LSeriesSummable
