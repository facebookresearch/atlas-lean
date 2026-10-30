/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace MathlibExt.Probability.ScottishBook161Wanted

/-- The central limit theorem conclusion for a frequency sequence `r`: for
any `a < b`, the Lebesgue measure in `[0, 1]` of the set of `x` with
`a < (sin(2π r₁ x) + ... + sin(2π rₙ x)) / √n < b` tends to
`(1 / √π) * ∫_a^b exp(-y²) dy`. -/
def LacunaryCLT (r : ℕ → ℤ) : Prop :=
  ∀ a b : ℝ, a < b →
    Filter.Tendsto
      (fun n : ℕ =>
        (MeasureTheory.volume {x : ℝ | x ∈ Set.Icc 0 1 ∧
          a < (∑ k ∈ Finset.range n, Real.sin (2 * Real.pi * (r k : ℝ) * x)) /
              Real.sqrt (n : ℝ) ∧
          (∑ k ∈ Finset.range n, Real.sin (2 * Real.pi * (r k : ℝ) * x)) /
              Real.sqrt (n : ℝ) < b}).toReal)
      Filter.atTop
      (nhds ((1 / Real.sqrt Real.pi) * MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Ioc a b)) (fun y => Real.exp (- y ^ 2))))

/--
The central limit theorem for lacunary trigonometric series holds under
Kac's gap hypothesis, and in particular for `rₙ = 2ⁿ`. More precisely: if
`(rₙ)` is a sequence of integers with `rₙ` minus the sum of all earlier
terms tending to infinity, then the central limit conclusion above holds;
and the same conclusion holds for `rₙ = 2ⁿ`, which does not satisfy the gap
hypothesis. The sequence `rₙ = 2^(n²)` is the example given in the problem
satisfying the hypothesis.
Source: M. Kac, Problem 161 of the Scottish Book; the `2ⁿ` case is affirmative
by R. Salem and A. Zygmund, "On lacunary trigonometric series", Proc. Natl.
Acad. Sci. USA 33 (1947), 333-338, who proved the central limit theorem for
lacunary trigonometric series with ratio bounded away from `1`.
-/
theorem_wanted kacLacunaryCentralLimitTheorem :
    (∀ r : ℕ → ℤ,
      Filter.Tendsto (fun n : ℕ => (r n - ∑ k ∈ Finset.range n, r k))
        Filter.atTop Filter.atTop → LacunaryCLT r) ∧
      LacunaryCLT (fun n : ℕ => (2 : ℤ) ^ n)

end MathlibExt.Probability.ScottishBook161Wanted
