/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Order.Filter.Basic

@[expose] public section

namespace MathlibExt.Probability.ScottishBook126Wanted

/--
Kac's Problem 126 from the Scottish Book: if `∫_0^1 f = 0` and
`∫_0^1 f^2 = ∞`, then
`[∫_0^1 exp (i f (x) / √n) dx]^n → 0` as `n → ∞`. Source: M. Kac,
Problem 126 of the Scottish Book; solved affirmatively by A. Khintchine,
fourth communique on dependent functions, Studia Mathematicae 6 or 7, as
cited in the typescript addendum Ad 126. The typescript parenthetical
states the finite-variance case as `e ^ (-1 / 2)` where `e ^ (-A / 2)` for
`A = ∫_0^1 f^2` would be expected; that parenthetical is not used here.
-/
theorem_wanted khintchine_infinite_variance_limit :
    ∀ f : ℝ → ℝ,
      Measurable f →
      MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) 1) MeasureTheory.volume →
      (∫ x in Set.Icc (0 : ℝ) 1, f x ∂MeasureTheory.volume) = 0 →
      (∫⁻ x in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal ((f x) ^ 2) ∂MeasureTheory.volume) = ⊤ →
      Filter.Tendsto
        (fun n : ℕ =>
          (∫ x in Set.Icc (0 : ℝ) 1,
            Complex.exp (Complex.I * (f x : ℂ) / (Real.sqrt (n : ℝ) : ℂ))
              ∂MeasureTheory.volume) ^ n)
        Filter.atTop (nhds (0 : ℂ))

end MathlibExt.Probability.ScottishBook126Wanted
