/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance

import MathlibExt.Probability.Statistics.Measurement.AffineLaws
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Means and variances under affine change of scale -/

open MeasureTheory ProbabilityTheory

namespace MetaMathlibExt

@[expose] public section

/-- **Means and variances under affine change of scale.** On a probability space, the map
$x \mapsto ax+b$ takes the mean of an integrable real random variable to $a$ times its mean
plus $b$. For a square-integrable variable it scales the variance by $a^2$. Differences of means
scale by $a$, so their ratios are invariant when $a$ and the original denominator are nonzero.
Ratios of means are invariant under nonzero scaling with nonzero denominator, but translation
can change them: shifting constants $1$ and $2$ by $1$ changes the ratio from $1/2$ to $2/3$.
An original ratio of one stays one under an affine change when both denominators are nonzero.

Source: Grinstead and Snell, *Introduction to Probability*, Dartmouth PDF dated July 4, 2006,
Theorems 6.2 and 6.7 for expectation and variance. The statements on ratios follow algebraically. -/
theorem affine_mean_variance_laws {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (a b : ℝ) :
    let M := fun Z : Ω → ℝ => ∫ ω, Z ω ∂μ
    let F := fun (Z : Ω → ℝ) ω => a * Z ω + b
    (∀ {X : Ω → ℝ}, Integrable X μ → M (F X) = a * M X + b) ∧
    (∀ {X : Ω → ℝ}, MemLp X 2 μ → variance (F X) μ = a ^ 2 * variance X μ) ∧
    (∀ {X Y : Ω → ℝ}, Integrable X μ → Integrable Y μ →
      M (F X) - M (F Y) = a * (M X - M Y)) ∧
    (∀ {X Y : Ω → ℝ}, Integrable X μ → Integrable Y μ → a ≠ 0 → M Y ≠ 0 →
      M (fun ω => a * X ω) / M (fun ω => a * Y ω) = M X / M Y) ∧
    (M (fun _ => 1) / M (fun _ => 2) = 1 / 2 ∧
      M (fun _ => 1 + 1) / M (fun _ => 2 + 1) = 2 / 3) ∧
    (∀ {X Y : Ω → ℝ}, Integrable X μ → Integrable Y μ →
      M Y ≠ 0 → M (F Y) ≠ 0 → M X / M Y = 1 → M (F X) / M (F Y) = 1) ∧
    (∀ {X Y U W : Ω → ℝ}, Integrable X μ → Integrable Y μ → Integrable U μ → Integrable W μ →
      a ≠ 0 → M U - M W ≠ 0 →
      (M (F X) - M (F Y)) / (M (F U) - M (F W)) = (M X - M Y) / (M U - M W)) := by
  let M := fun Z : Ω → ℝ => ∫ ω, Z ω ∂μ
  let F := fun (Z : Ω → ℝ) ω => a * Z ω + b
  have hmean {Z : Ω → ℝ} (hZ : Integrable Z μ) : M (F Z) = a * M Z + b :=
    integral_const_mul_add_const hZ
  have hdiff {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ) :
      M (F X) - M (F Y) = a * (M X - M Y) := by
    rw [hmean hX, hmean hY]
    ring
  refine ⟨@hmean, ?_, @hdiff, ?_, ?_, ?_, ?_⟩
  · intro X hX
    exact variance_const_mul_add_const hX.aestronglyMeasurable
  · intro X Y _ _ ha _
    dsimp only [M]
    simp only [integral_const_mul, mul_div_mul_left _ _ ha]
  · simp [show (1 : ℝ) + 1 = 2 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num]
  · intro X Y hX hY hY₀ hFY₀ hratio
    change M (F X) / M (F Y) = 1
    have heq : M X = M Y := by simpa only [one_mul] using (div_eq_iff hY₀).mp hratio
    have hFeq : M (F X) = M (F Y) := by rw [hmean hX, hmean hY, heq]
    rw [hFeq, div_self hFY₀]
  · intro X Y U W hX hY hU hW ha hden
    change (M (F X) - M (F Y)) / (M (F U) - M (F W)) = (M X - M Y) / (M U - M W)
    rw [hmean hX, hmean hY, hmean hU, hmean hW]
    exact MathlibExt.Probability.Statistics.Measurement.affine_sub_div_affine_sub
      ha (M X) (M Y) (M U) (M W) hden

end

end MetaMathlibExt
