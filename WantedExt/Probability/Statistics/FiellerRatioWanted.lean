/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fieller's confidence sets for a ratio of means

Let `(a, b)` be jointly Gaussian with known variances `v_aa, v_bb` and covariance `v_ab`. For any
parameter `θ` satisfying `E a = θ E b` with positive variance `V(θ) = v_aa - 2 θ v_ab + θ² v_bb`
(`V(θ) > 0`), `a - θ b` is centered Gaussian with variance `V(θ)`, so the set
`{θ | (a - θ b)² ≤ z² V(θ)}` covers `θ` with exact probability `P(|N(0, 1)| ≤ z)`, which is `1 - α`
for the two-sided normal quantile `z`. When `E b ≠ 0`, this parameter is the uniquely identified
ratio `θ = E a / E b` (if `E a = E b = 0`, every `θ` satisfies `E a = θ E b` and there is no
identified ratio). The set is the solution set of a quadratic inequality in `θ`: a bounded interval
containing `a / b` when `b² > z² v_bb`, and the whole line or the complement of a bounded open
interval when `b² < z² v_bb`.

Sources: E. C. Fieller, "Some problems in interval estimation", J. R. Statist. Soc. B 16 (1954)
175–185; E. C. Fieller, "The biological standardization of insulin", Suppl. J. R. Statist. Soc.
7 (1940) 1–64.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Covariance
public import MathlibExt.Probability.Statistics.FiellerRatio
