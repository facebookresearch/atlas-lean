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

/-- Scottish Book Problem 124, sub-conjecture: if `f` is continuous
and `f 0 ≠ 0`, then the integral equation `∫_0^x y(t) f(x - t) dt = 0`
for `0 ≤ x ≤ 1` has only the solution `y = 0`. `y` is read as an
integrable function on `[0, 1]` (the typescript does not specify a
function class for `y`; the `L^2` context in the entry motivates the
integrable reading) and "y ≡ 0" is read as `y = 0` almost everywhere
with respect to Lebesgue measure restricted to `[0, 1]`. `f` is read
as continuous on all of `ℝ`; only its values on `[-1, 1]` are used.
TYPESCRIPT TYPO, CORRECTED (Phase 5): the typescript prints the
equation as `∫₀¹ y(t) f(x-t) dt = 0`, but the entry's own arguments
on the same page show the intended upper limit is `x` (Volterra
form): with upper limit `1` the entry's "known" claims are false
(`f ≡ 1`, `y(t) = t - 1/2` is a non-zero solution), while with
upper limit `x` the iterated-integral argument coheres — an
iterated integral of a solution again satisfies the equation. -/
def ScottishBookProblem124Claim : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f → f 0 ≠ 0 →
    ∀ (y : ℝ → ℝ),
      MeasureTheory.IntegrableOn y (Set.Icc (0 : ℝ) 1) MeasureTheory.volume →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∫ t in (0 : ℝ)..x, y t * f (x - t) = 0) →
      y =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)] 0

/--
Marcinkiewicz's Problem 124 sub-conjecture holds (solved-positive).
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
