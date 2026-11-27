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

@[expose] public section

namespace WantedExt.Probability.Statistics.FiellerRatioWanted

open MeasureTheory ProbabilityTheory

/-- **Exact coverage of Fieller's set.** Let `μ` be a probability measure and let
`(a, b) : Ω → ℝ × ℝ` have a Gaussian law under `μ`, with `Var a = v_aa`, `Var b = v_bb`,
`Cov(a, b) = v_ab` and means satisfying `E a = θ E b`. Assume
`V(θ) = v_aa - 2 θ v_ab + θ² v_bb > 0` and let `z > 0`. Then the probability that `θ` lies in
Fieller's set computed from `(a, b)` equals the standard Gaussian probability of `[-z, z]`.

Sources: E. C. Fieller, "Some problems in interval estimation", J. R. Statist. Soc. B 16 (1954)
175–185; E. C. Fieller, "The biological standardization of insulin", Suppl. J. R. Statist. Soc. 7
(1940) 1–64. -/
public theorem_wanted measureReal_mem_fiellerSet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (a b : Ω → ℝ) (hG : HasGaussianLaw (fun ω => (a ω, b ω)) μ)
    (vaa vab vbb θ z : ℝ) (hvaa : Var[a; μ] = vaa) (hvbb : Var[b; μ] = vbb)
    (hvab : cov[a, b; μ] = vab) (hmean : ∫ ω, a ω ∂μ = θ * ∫ ω, b ω ∂μ)
    (hV : 0 < vaa - 2 * θ * vab + θ ^ 2 * vbb) (hz : 0 < z) :
    μ.real {ω | θ ∈ fiellerSet (a ω) (b ω) vaa vab vbb z} =
      (gaussianReal 0 1).real (Set.Icc (-z) z)

end WantedExt.Probability.Statistics.FiellerRatioWanted
