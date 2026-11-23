/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovContinuity

@[expose] public section

namespace MathlibExtTest.Probability.KolmogorovContinuity

/-- The deterministic chaining lemma applied to `f = id`: the identity is
`1 / 2`-Hölder on the dyadic rationals of `[0, 1]` with the explicit
chaining constant. -/
example :
    ∀ q r : ℝ,
      q ∈ MathlibExt.Probability.KolmogorovContinuity.dyadicRationals ∩ Set.Icc 0 1 →
      r ∈ MathlibExt.Probability.KolmogorovContinuity.dyadicRationals ∩ Set.Icc 0 1 →
      |q - r| ≤ (4 + 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))))
        * |q - r| ^ (1 / 2 : ℝ) := by
  intro q r hq hr
  have h := MathlibExt.Probability.KolmogorovContinuity.dyadic_holder_of_increment_bound
    (f := id) (γ := (1 / 2 : ℝ)) (D := 1) (by norm_num) (by norm_num) (by
      intro m k _
      show |((k : ℝ) + 1) / (2 : ℝ) ^ m - (k : ℝ) / (2 : ℝ) ^ m|
          ≤ 1 * (2 : ℝ) ^ (-(m : ℝ) * (1 / 2 : ℝ))
      have e1 : |((k : ℝ) + 1) / (2 : ℝ) ^ m - (k : ℝ) / (2 : ℝ) ^ m|
          = 1 / (2 : ℝ) ^ m := by
        rw [div_sub_div_same, show ((k : ℝ) + 1 - (k : ℝ)) = 1 by ring,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ m)]
      rw [e1]
      have e2 : (1 : ℝ) / (2 : ℝ) ^ m = (2 : ℝ) ^ (-(m : ℝ)) := by
        rw [one_div, ← Real.rpow_natCast (2 : ℝ) m,
          ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [e2, one_mul]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
        linarith)) hq hr
  simpa using h

/-- The main theorem on the constant process: for every `γ < 1 / 2` there is
a modification that is a.s. `γ`-Hölder on the dyadics. -/
example :
    ∀ γ : ℝ, γ < (1 : ℝ) / 2 → γ > 0 →
      ∃ Y : ℝ → Unit → ℝ,
        (∀ t, ∀ᵐ ω ∂(MeasureTheory.Measure.dirac ()), Y t ω = 0) ∧
        (∀ᵐ ω ∂(MeasureTheory.Measure.dirac ()), ∃ C : ℝ, 0 < C ∧
          ∀ q r : ℝ,
            q ∈ MathlibExt.Probability.KolmogorovContinuity.dyadicRationals ∩ Set.Icc 0 1 →
            r ∈ MathlibExt.Probability.KolmogorovContinuity.dyadicRationals ∩ Set.Icc 0 1 →
            |Y q ω - Y r ω| ≤ C * |q - r| ^ γ) := by
  intro γ hγ1 hγ0
  refine MathlibExt.Probability.KolmogorovContinuity.kolmogorov_continuity_theorem
    (X := fun _ _ => (0 : ℝ)) (μ := MeasureTheory.Measure.dirac ()) (α := 1) (β := 2) (K := 1)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ γ hγ1 hγ0
  · intro s t
    have h0 : (fun ω : Unit =>
        |(fun _ _ => (0 : ℝ)) s ω - (fun _ _ => (0 : ℝ)) t ω| ^ (2 : ℝ))
        = fun _ => (0 : ℝ) := by
      funext ω
      simp only [sub_self, abs_zero]
      rw [Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
    rw [h0]
    exact MeasureTheory.integrable_const _
  · intro s t
    have h0 : (fun ω : Unit =>
        |(fun _ _ => (0 : ℝ)) s ω - (fun _ _ => (0 : ℝ)) t ω| ^ (2 : ℝ))
        = fun _ => (0 : ℝ) := by
      funext ω
      simp only [sub_self, abs_zero]
      rw [Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
    rw [h0, MeasureTheory.integral_const, smul_zero]
    positivity

/-- The main theorem on `X_t(⋆) = t`: the identity process satisfies the
moment bound with `α = 1`, `β = 2`, `K = 1`, so it has a Hölder
modification for every `γ < 1 / 2`. -/
example :
    ∀ γ : ℝ, γ < (1 : ℝ) / 2 → γ > 0 →
      ∃ Y : ℝ → Unit → ℝ,
        (∀ t, ∀ᵐ ω ∂(MeasureTheory.Measure.dirac ()), Y t ω = t) ∧
        (∀ᵐ ω ∂(MeasureTheory.Measure.dirac ()), ∃ C : ℝ, 0 < C ∧
          ∀ q r : ℝ,
            q ∈ MathlibExt.Probability.KolmogorovContinuity.dyadicRationals ∩ Set.Icc 0 1 →
            r ∈ MathlibExt.Probability.KolmogorovContinuity.dyadicRationals ∩ Set.Icc 0 1 →
            |Y q ω - Y r ω| ≤ C * |q - r| ^ γ) := by
  intro γ hγ1 hγ0
  refine MathlibExt.Probability.KolmogorovContinuity.kolmogorov_continuity_theorem
    (X := fun t _ => t) (μ := MeasureTheory.Measure.dirac ()) (α := 1) (β := 2) (K := 1)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ γ hγ1 hγ0
  · intro s t
    show MeasureTheory.Integrable (fun _ : Unit => |s - t| ^ (2 : ℝ)) (MeasureTheory.Measure.dirac ())
    exact MeasureTheory.integrable_const _
  · intro s t
    show ∫ _ω : Unit, |s - t| ^ (2 : ℝ) ∂(MeasureTheory.Measure.dirac ()) ≤ 1 * |s - t| ^ (1 + 1)
    rw [MeasureTheory.integral_const]
    show ((MeasureTheory.Measure.dirac () Set.univ).toReal) • |s - t| ^ (2 : ℝ)
      ≤ 1 * |s - t| ^ (1 + 1)
    rw [MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ ()),
      ENNReal.toReal_one, one_smul, one_mul, show (1 : ℝ) + 1 = (2 : ℝ) by norm_num]

end MathlibExtTest.Probability.KolmogorovContinuity
