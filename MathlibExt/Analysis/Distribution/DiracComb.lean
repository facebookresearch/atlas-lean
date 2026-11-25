/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The Dirac comb

The sum of the unit point masses at the integers defines a tempered distribution on the real line.
-/

public section

open MeasureTheory
open scoped SchwartzMap BigOperators

namespace MathlibExt.Analysis.Distribution.TemperedExamplesWanted

/--
**The Dirac comb is a tempered distribution.** There is a tempered distribution $T$ on
$\mathbb{R}$, that is, a continuous $\mathbb{C}$-linear functional on the space of
complex-valued Schwartz functions on $\mathbb{R}$, such that $T(g)=\sum_{n\in\mathbb{Z}} g(n)$
for every complex-valued Schwartz function $g$ on $\mathbb{R}$.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Tempered distributions" / entry "Dirac comb";
<https://en.wikipedia.org/wiki/Dirac_comb>.
-/
theorem diracComb_toTemperedDistribution :
    ∃ T : 𝓢'(ℝ, ℂ), ∀ g : 𝓢(ℝ, ℂ), T g = ∑' n : ℤ, g (n : ℝ) := by
  let μ := Measure.sum fun n : ℤ ↦ Measure.dirac (n : ℝ)
  have : μ.HasTemperateGrowth := by
    refine ⟨⟨2, integrable_sum_measure (fun n ↦ integrable_dirac (by simp)) ?_⟩⟩
    -- On either half of the integer lattice, the weight is the shifted inverse-square series.
    have h := (summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ) ^ (-(2 : ℝ))) 1).2
      (Real.summable_nat_rpow.mpr (by norm_num))
    apply Summable.of_nat_of_neg <;>
      simpa [Real.norm_of_nonneg, Real.rpow_nonneg, add_comm] using h
  refine ⟨μ.toTemperedDistribution, fun g ↦ ?_⟩
  calc
    μ.toTemperedDistribution g = ∫ x, g x ∂μ := μ.toTemperedDistribution_apply g
    _ = ∑' n : ℤ, g (n : ℝ) := by
      simpa only [integral_dirac] using integral_sum_measure (g.integrable (μ := μ))

end MathlibExt.Analysis.Distribution.TemperedExamplesWanted
