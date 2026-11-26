/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BerryEsseenModel
import Mathlib.Tactic.Linarith
import MathlibExt.Probability.Distributions.GaussianCdf

/-! # Left and right CDF conventions for the Berry–Esseen error -/

@[expose] public section

open Filter Function MeasureTheory ProbabilityTheory Set BerryEsseenModel
open scoped Topology

namespace BerryEsseenWanted

/-- **Statement of the Kolmogorov distance via left-continuous distribution functions.** This is
the proposition that for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance
$1$ and finite third absolute moment and every integer $n \ge 1$, if $S_n = X_1 + \dots + X_n$ for
independent random variables $X_1, X_2, \dots$ each with law $\mu$, then
$$
\sup_{x \in \mathbb{R}} \bigl|P(S_n/\sqrt{n} < x) - \Phi(x)\bigr|
= \sup_{x \in \mathbb{R}} \bigl|P(S_n/\sqrt{n} \le x) - \Phi(x)\bigr|,
$$
where $\Phi$ is the standard normal distribution function.

Source: the right-CDF catalogue definition and retained Shevtsova2011
lines 104-108, which explicitly use a left-continuous CDF. This probability
bridge is requested, not inferred by replacing strict with non-strict events. -/
def leftRightCDFErrorEquivalence : Prop :=
  ∀ μ : Measure ℝ, IsStandardizedLaw μ → ∀ n : ℕ+,
    sSup (Set.range (fun x : ℝ ↦
      |(normalizedLaw μ n).real (Set.Iio x) - normalCDF x|)) = kolmogorovError μ n

/-- **Kolmogorov distance via left-continuous distribution functions.** Let $\mu$ be a probability
measure on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute moment, let $n \ge 1$
be an integer, and let $S_n = X_1 + \dots + X_n$ for independent random variables $X_1, X_2, \dots$
each with law $\mu$. Then
$$
\sup_{x \in \mathbb{R}} \bigl|P(S_n/\sqrt{n} < x) - \Phi(x)\bigr|
= \sup_{x \in \mathbb{R}} \bigl|P(S_n/\sqrt{n} \le x) - \Phi(x)\bigr|,
$$
where $\Phi$ is the standard normal distribution function.

Source: catalogue C19a right CDF and Shevtsova2011's explicit left convention. -/
theorem leftRightCDFErrorEquivalence_holds : leftRightCDFErrorEquivalence := by
  intro μ hμ n
  let ν := normalizedLaw μ n
  let : IsProbabilityMeasure ν := normalizedLaw_probability hμ n
  let F := cdf ν
  let γ := gaussianReal 0 1
  let G := cdf γ
  have hG : Continuous (G : ℝ → ℝ) := continuous_cdf_gaussianReal 0 one_ne_zero
  have hFnonneg (x : ℝ) : 0 ≤ leftLim (F : ℝ → ℝ) x :=
    ge_of_tendsto (F.mono.tendsto_leftLim x) (Eventually.of_forall (cdf_nonneg ν))
  have hIio (x : ℝ) : ν.real (Iio x) = leftLim (F : ℝ → ℝ) x := by
    rw [measureReal_def, ← measure_cdf ν, StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot ν),
      sub_zero, ENNReal.toReal_ofReal (hFnonneg x)]
  have hL : BddAbove (range fun x : ℝ => |leftLim (F : ℝ → ℝ) x - G x|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h₁ := hFnonneg x
    have h₂ := (F.mono.leftLim_le (le_refl x)).trans (cdf_le_one ν x)
    have h₃ := cdf_nonneg γ x
    have h₄ := cdf_le_one γ x
    rw [abs_le]
    constructor <;> linarith
  have hR (x : ℝ) : Tendsto (leftLim (F : ℝ → ℝ)) (𝓝[>] x) (𝓝 (F x)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((F.right_continuous x).mono fun _ hy => le_of_lt hy).tendsto ?_ ?_
    · filter_upwards [self_mem_nhdsWithin (s := Ioi x)] with y hy
      exact F.mono.le_leftLim hy
    · exact Eventually.of_forall fun _ => F.mono.leftLim_le le_rfl
  change sSup (range fun x : ℝ => |ν.real (Iio x) - G x|) = kolmogorovError μ n
  simp_rw [hIio]
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact le_of_tendsto ((F.mono.tendsto_leftLim x).sub
        (hG.continuousAt.continuousWithinAt : ContinuousWithinAt G (Iio x) x)).abs
      (Eventually.of_forall (pointwise_le_kolmogorovError μ n))
  · apply (error_le_iff μ n _).2
    intro x
    exact le_of_tendsto ((hR x).sub
        (hG.continuousAt.continuousWithinAt : ContinuousWithinAt G (Ioi x) x)).abs
      (Eventually.of_forall fun y => le_csSup hL ⟨y, rfl⟩)

end BerryEsseenWanted
