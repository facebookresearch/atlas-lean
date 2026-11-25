/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.ContinuousOn

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook124Wanted

/-- **The Volterra-form sub-conjecture of Scottish Book Problem 124.** The statement that for every
continuous function $f : \mathbb{R} \to \mathbb{R}$ with $f(0) \ne 0$ and every function
$y : \mathbb{R} \to \mathbb{R}$ that is Lebesgue integrable on $[0, 1]$, if
$\int_0^x y(t) f(x - t)\,dt = 0$ for every $x \in [0, 1]$, then $y = 0$ almost everywhere on
$[0, 1]$.

The Scottish Book typescript prints the upper limit of the integral as $1$, but the entry's own
arguments show that the intended upper limit is $x$ (Volterra form); with upper limit $1$ the
claim is false, since $f \equiv 1$ and $y(t) = t - 1/2$ give a nonzero solution. The typescript
does not specify a function class for $y$; integrability on $[0, 1]$ is motivated by the $L^2$
context of the entry. -/
def ScottishBookProblem124Claim : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f → f 0 ≠ 0 →
    ∀ (y : ℝ → ℝ),
      MeasureTheory.IntegrableOn y (Set.Icc (0 : ℝ) 1) MeasureTheory.volume →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∫ t in (0 : ℝ)..x, y t * f (x - t) = 0) →
      y =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)] 0

/--
**The Volterra-form sub-conjecture of Scottish Book Problem 124 holds.** For every continuous
function $f : \mathbb{R} \to \mathbb{R}$ with $f(0) \ne 0$ and every function
$y : \mathbb{R} \to \mathbb{R}$ that is Lebesgue integrable on $[0, 1]$, if
$\int_0^x y(t) f(x - t)\,dt = 0$ for every $x \in [0, 1]$, then $y = 0$ almost everywhere on
$[0, 1]$.

Source: Józef Marcinkiewicz, Problem 124 of the Scottish Book;
typescript PDF p.58, printed p.55.
TYPESCRIPT TYPO, CORRECTED (Phase 5): the typescript prints the
equation as `∫₀¹ y(t) f(x-t) dt = 0`, but the intended upper limit
is `x` (Volterra form). The literal `∫₀¹` reading is false: `f ≡ 1`,
`y(t) = t - 1/2` is a nonzero solution. Only the Volterra `∫₀ˣ`
reading is filed here.
Positive by the local Titchmarsh convolution theorem: E. C.
Titchmarsh, "The zeros of certain integral functions", Proc. London
Math. Soc. s2-25 (1926), 283–302, DOI 10.1112/plms/s2-25.1.283.
Sketch: Titchmarsh gives `λ, μ ≥ 0` with `λ + μ ≥ 1` such that
`y = 0` a.e. on `(0, λ)` and `f = 0` a.e. on `(0, μ)`. Continuity
of `f` at `0` with `f 0 ≠ 0` forces `μ = 0` (otherwise `f` would be
a.e. zero on a positive-measure initial interval while being nonzero
near `0`), so `λ ≥ 1` and `y = 0` a.e. on `[0, 1]`.
-/
theorem_wanted marcinkiewicz124_holds : ScottishBookProblem124Claim

end MathlibExt.Analysis.ScottishBook124Wanted
