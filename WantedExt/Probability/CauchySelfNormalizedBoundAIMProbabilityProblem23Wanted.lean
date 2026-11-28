/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A time-uniform self-normalized bound for Cauchy sums (AimPL Stein's method, Problem 1.15)

AimPL, Stein's method and applications in high-dimensional statistics, Problem 1.15: for i.i.d.
symmetric Cauchy `X₁, X₂, …`, `S_t = ∑_{i ≤ t} X_i` and `V_t = ∑_{i ≤ t} X_i²`, prove with Stein's
method that `P(∃ t ∈ ℕ, S_t / (V_t + m) > x) ≤ e^{-2 m x²}` for all `m, x ≥ 0`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Probability.Independence.Basic
public import MathlibExt.Probability.CauchySelfNormalizedBoundAIMProbabilityProblem23

@[expose] public section

namespace MathlibExt.Probability.CauchySelfNormalizedBoundAIMProbabilityProblem23Wanted

/-!
Source: AimPL: Stein's method and applications in high-dimensional statistics, Problem 1.15,
http://aimpl.org/steinhd/1/ (remark: the inequality is Example 4 of arXiv:1808.03204 and holds for
any symmetric increments). UnsolvedMath record UM-20002581 (`AIM-PROBABILITY-0023`), dataset
ulamai/UnsolvedMath v1.8.0.

The variables are i.i.d. standard Cauchy (location `0`, scale `1`; Mathlib's `cauchyMeasure 0 1`),
as in Howard et al.'s example; scaling the variables by `γ > 0` turns the event for `(m, x)` into
the event for `(m / γ², γ x)`, which has the same bound `e^{-2 m x²}`, so scale `1` loses nothing.
`S_t` and `V_t` sum the first `t` variables (`t = 0` gives `0`, which never exceeds `x ≥ 0`). When
`m = 0` or `x = 0` the bound is `1`. The request to use Stein's method is a proof-method requirement
and is not formalized; the AimPL remark records that the inequality itself is known.
-/

open MeasureTheory ProbabilityTheory

end MathlibExt.Probability.CauchySelfNormalizedBoundAIMProbabilityProblem23Wanted
