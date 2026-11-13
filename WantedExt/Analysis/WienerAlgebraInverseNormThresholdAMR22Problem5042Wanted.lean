/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bounding inverses in the analytic Wiener algebra (Hayman–Lingham Problem 5.42)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 5.42 (H. S. Shapiro):
for `f = ∑ aₙ zⁿ` with `∑ |aₙ| = 1`, `|f| ≥ δ > 0` in the unit disc and `1/f = ∑ bₙ zⁿ`, what is the
infimum of those `δ` for which `M = ∑ |bₙ|` can be bounded in terms of `δ`? (A likely guess is
`1/2`.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace MathlibExt.Analysis.WienerAlgebraInverseNormThresholdAMR22Problem5042Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 5.42 (H. S. Shapiro). UnsolvedMath record UM-02305042
(`AMR-022-5042`), dataset ulamai/UnsolvedMath v1.8.0.

`InverseBounded δ` says that some `M` bounds `∑ |bₙ|` (all partial sums) for every `f = ∑ aₙ zⁿ`
with `∑ |aₙ| ≤ 1` and `|f| ≥ δ` on the open disc; the coefficients `bₙ` of `1/f` are characterized
by `HasSum` on the open disc. The normalization `∑ |aₙ| ≤ 1` is Nikolski's (`‖f‖_{W₊} ≤ 1` in his
definition (0.2.5) of `c₁(δ)`); the problem normalizes `∑ |aₙ| = 1`. The answer is stated as `sInf
{δ > 0 | InverseBounded δ} = 1/2`, Nikolski's `δ₁(W₊, 𝔻) = 1/2`; for `f ∈ W₊`, `|f| ≥ δ` on the open
disc is the same as on the closed disc of bounded characters of `ℤ₊` used there.
-/

/-- `M` bounds the inverse coefficients at level `δ`: whenever `f(z) = ∑ aₙ zⁿ` has
`∑ |aₙ| ≤ 1` (Nikolski's normalization `‖f‖_{W₊} ≤ 1`) and `|f(z)| ≥ δ` on the unit disc, the
Taylor coefficients `bₙ` of `1 / f` satisfy `∑ |bₙ| ≤ M` (stated for all partial sums). -/
def InverseBoundedBy (δ M : ℝ) : Prop :=
  ∀ a b : ℕ → ℂ, Summable (fun n => ‖a n‖) → ∑' n, ‖a n‖ ≤ 1 →
    (∀ z ∈ Metric.ball (0 : ℂ) 1, δ ≤ ‖∑' n, a n * z ^ n‖) →
    (∀ z ∈ Metric.ball (0 : ℂ) 1, HasSum (fun n => b n * z ^ n) (∑' n, a n * z ^ n)⁻¹) →
    ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖b n‖ ≤ M

/-- `M = ∑ |bₙ|` can be bounded in terms of `δ`. -/
def InverseBounded (δ : ℝ) : Prop :=
  ∃ M : ℝ, InverseBoundedBy δ M

/-- Hayman–Lingham Problem 5.42 (H. S. Shapiro), answered in Nikolski's normalization: the infimum
of those `δ > 0` for which `M = ∑ |bₙ|` can be bounded in terms of `δ` is `1 / 2`. -/
def criticalDeltaIsOneHalf : Prop :=
  sInf {δ : ℝ | 0 < δ ∧ InverseBounded δ} = 1 / 2

/--
Resolved true: Nikolski proved that for the analytic Wiener algebra `W₊` of absolutely convergent
Taylor series the critical constant is `δ₁(W₊, 𝔻) = 1/2`: if `‖f‖_{W₊} ≤ 1` and `|f| ≥ δ` on the
disc, then `‖f⁻¹‖_{W₊} ≤ 1/(2δ - 1)` for `δ > 1/2`, while no bound exists for `δ ≤ 1/2`, confirming
Shapiro's guess (Katznelson had the unbounded range `δ < 1/2`). Source: W. K. Hayman and E. F.
Lingham, Research Problems in Function Theory, Fiftieth Anniversary Edition (2019),
arXiv:1809.07200, Problem 5.42 (H. S. Shapiro); resolution: N. Nikolski, In search of the invisible
spectrum, Ann. Inst. Fourier (Grenoble) 49 (1999), no. 6, 1925-1998, Theorem B with Section 2.3.1 (S
= ℤ₊, whose bounded characters fill the closed disc 𝔻): δ₁(W₊, 𝔻) = 1/2 and c₁(δ, W₊, 𝔻) = 1/(2δ -
1) for 1/2 < δ ≤ 1, where by (0.2.5) c₁(δ) = sup{‖f⁻¹‖ : f ∈ W₊, δ ≤ |f(z)| for z ∈ 𝔻, ‖f‖ ≤ 1} and
δ₁ = inf{δ : c₁(δ) < ∞}; Subsection 3.3 shows c₁(δ) = ∞ for δ ≤ 1/2,
https://doi.org/10.5802/aif.1743.
-/
public theorem_wanted criticalDeltaIsOneHalf_holds : criticalDeltaIsOneHalf

end MathlibExt.Analysis.WienerAlgebraInverseNormThresholdAMR22Problem5042Wanted
