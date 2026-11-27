/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Medians minimize the expected absolute deviation

* `IsMedian ν m`: `m` is a median of the probability measure `ν` on `ℝ`, that is, each of
  `(-∞, m]` and `[m, ∞)` has probability at least `1 / 2`. Medians need not be unique.
* `integral_abs_sub_le_of_isMedian`: every median `m` minimizes `y ↦ ∫ |θ - y| dν(θ)`. Without a
  first moment both sides are `0` by the convention for non-integrable functions.

MathlibExt's `ProbabilityTheory.cdfQuantile` (`MathlibExt/Probability/Quantile.lean`) gives the
generalized inverse of the cdf, whose value at `1 / 2` is a median.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Set

/-- **Median of a measure on the real line.** Let $\nu$ be a measure on $\mathbb{R}$, typically a
probability measure. A real number $m$ is a median of $\nu$ when $\nu((-\infty, m]) \ge 1/2$
and $\nu([m, \infty)) \ge 1/2$, where a set of infinite measure counts as having measure $0$. -/
def IsMedian (ν : Measure ℝ) (m : ℝ) : Prop :=
  1 / 2 ≤ ν.real (Iic m) ∧ 1 / 2 ≤ ν.real (Ici m)

/-- **Absolute deviations are integrable exactly when the mean exists.** Let $\nu$ be a finite
measure on $\mathbb{R}$ and let $c \in \mathbb{R}$. Then $\theta \mapsto |\theta - c|$ is
$\nu$-integrable if and only if $\theta \mapsto \theta$ is $\nu$-integrable. -/
theorem integrable_abs_sub_iff (ν : Measure ℝ) [IsFiniteMeasure ν] (c : ℝ) :
    Integrable (fun θ => |θ - c|) ν ↔ Integrable (fun θ : ℝ => θ) ν := by
  have h : (fun θ : ℝ => |θ - c|) = fun θ => ‖θ + -c‖ := by
    funext θ
    rw [Real.norm_eq_abs, sub_eq_add_neg]
  rw [h, integrable_norm_iff (by fun_prop), integrable_add_const_iff]

/-- The integral comparison behind the median: if `G ≤ F + c (2 · 1_S - 1)` with `c ≥ 0` and
`ν(S) ≤ 1 / 2`, then `∫ G ≤ ∫ F`. -/
private theorem integral_le_of_le_add_indicator (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {F G : ℝ → ℝ} {S : Set ℝ} {c : ℝ} (hF : Integrable F ν) (hG : Integrable G ν)
    (hS : MeasurableSet S) (hc : 0 ≤ c) (hνS : ν.real S ≤ 1 / 2)
    (h : ∀ θ, G θ ≤ F θ + c * (2 * S.indicator 1 θ - 1)) : ∫ θ, G θ ∂ν ≤ ∫ θ, F θ ∂ν := by
  have hind : Integrable (S.indicator (1 : ℝ → ℝ)) ν := (integrable_const 1).indicator hS
  have hlin : Integrable (fun θ => c * (2 * S.indicator 1 θ - 1)) ν :=
    ((hind.const_mul 2).sub (integrable_const 1)).const_mul c
  have hsum : Integrable (fun θ => F θ + c * (2 * S.indicator 1 θ - 1)) ν := hF.add hlin
  refine (integral_mono hG hsum h).trans ?_
  rw [integral_add hF hlin, integral_const_mul,
    integral_sub (hind.const_mul 2) (integrable_const 1), integral_const_mul,
    integral_indicator_one hS, integral_const, probReal_univ, one_smul]
  nlinarith

/-- **A median minimizes the expected absolute loss.** Let $\nu$ be a probability measure on
$\mathbb{R}$ and let $m$ be a median of $\nu$. Then for every $y \in \mathbb{R}$,
$$
\int |\theta - m| \, d\nu(\theta) \le \int |\theta - y| \, d\nu(\theta).
$$

When $\nu$ has no first moment, neither integrand is integrable and both integrals are $0$ by
the convention for non-integrable functions. -/
theorem integral_abs_sub_le_of_isMedian (ν : Measure ℝ) [IsProbabilityMeasure ν] {m : ℝ}
    (hm : IsMedian ν m) (y : ℝ) : ∫ θ, |θ - m| ∂ν ≤ ∫ θ, |θ - y| ∂ν := by
  by_cases hint : Integrable (fun θ => |θ - y|) ν
  swap
  · have hmint : ¬Integrable (fun θ => |θ - m|) ν := fun h =>
      hint ((integrable_abs_sub_iff ν y).mpr ((integrable_abs_sub_iff ν m).mp h))
    rw [integral_undef hmint, integral_undef hint]
  have hmint := (integrable_abs_sub_iff ν m).mpr ((integrable_abs_sub_iff ν y).mp hint)
  rcases le_total m y with hmy | hym
  · refine integral_le_of_le_add_indicator (S := Ioi m) ν hint hmint measurableSet_Ioi
      (sub_nonneg.mpr hmy)
      ?_ fun θ => ?_
    · rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
      linarith [hm.1]
    · by_cases hθ : m < θ
      · rw [indicator_of_mem (mem_Ioi.mpr hθ), Pi.one_apply]
        have := abs_sub_le θ y m
        rw [abs_of_nonneg (sub_nonneg.mpr hmy)] at this
        linarith
      · rw [indicator_of_notMem (by simpa using hθ)]
        push Not at hθ
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  · refine integral_le_of_le_add_indicator (S := Iio m) ν hint hmint measurableSet_Iio
      (sub_nonneg.mpr hym)
      ?_ fun θ => ?_
    · rw [← compl_Ici, probReal_compl_eq_one_sub measurableSet_Ici]
      linarith [hm.2]
    · by_cases hθ : θ < m
      · rw [indicator_of_mem (mem_Iio.mpr hθ), Pi.one_apply]
        have := abs_sub_le θ y m
        rw [abs_of_nonpos (sub_nonpos.mpr hym)] at this
        linarith
      · rw [indicator_of_notMem (by simpa using hθ)]
        push Not at hθ
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith

end ProbabilityTheory
