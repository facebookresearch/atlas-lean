/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.KarushKuhnTucker

/-! # KKT sufficiency

Aggregate entry point for the sufficiency core of roadmap package ML-22
of the Atlas TCS canon roadmap. It re-exports
`MathlibExt.Analysis.Convex.KarushKuhnTucker` and adds no declarations.

The sufficiency theorem is
`MathlibExt.Analysis.Convex.KarushKuhnTucker.isMinOn_of_karush_kuhn_tucker_convex`:
if `f` and every `g i` are convex on the whole space and differentiable
at `x`, and multipliers `lam i ≥ 0` satisfy complementary slackness
(`lam i * g i x = 0`) and stationarity
(`fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x = 0`), then
`IsMinOn f {y | ∀ i, g i y ≤ 0} x`, that is, `f x ≤ f y` for every
feasible `y`. That bound does not assume primal feasibility of `x`;
`x` is a minimizer over the feasible set only when, in addition,
`∀ i, g i x ≤ 0`.

Slater's condition and KKT necessity are follow-ups.

Source: Boyd and Vandenberghe, Convex Optimization (2004),
Section 5.5.3.
-/
