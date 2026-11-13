/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Angular synchronization by the projected power method (Bandeira, Open Problem 10.1)

Bandeira, Ten Lectures and Forty-Two Open Problems, Open Problem 10.1: in the model `C = z z* + σ
W`, does the projected power method `x ↦ ((C x)_k / |(C x)_k|)_k` converge with high probability to
the optimal solution of angular synchronization, `max x* C x` over `|x_k| = 1`, when the Gaussian
noise is small enough (for which values of `σ`)?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Probability.AngularSynchronizationShared

@[expose] public section

namespace MathlibExt.Probability.AngularSynchronizationPowerMethodAMR27Problem1001Wanted

/-!
Source: A. S. Bandeira, Ten Lectures and Forty-Two Open Problems in the Mathematics of Data Science
(2015-2016), Section 10.2, Open Problem 10.1,
https://afonsobandeira.wordpress.com/2015/12/09/42l10psynchronization/. UnsolvedMath record
UM-02801001 (`AMR-027-1001`), dataset ulamai/UnsolvedMath v1.8.0.

The noise model, problem (P) and uniqueness up to a global phase are those of
`WantedExt/Probability/AngularSynchronizationShared.lean` (Zhong-Boumal, Section 1). The method is
Algorithm 1 of Zhong and Boumal (generalized power method without shift), which is Bandeira's
Algorithm 10.1 started at a leading eigenvector: `x₀` is a leading eigenvector of `C` with `‖x₀‖₂ =
√n` (for Hermitian `C`, a maximizer of `x* C x` on the sphere `‖x‖₂² = n`), and `x_{t+1} = P(C x_t)`
with `P(a)_k = a_k / |a_k|` (`1` when `a_k = 0`). Bandeira allows any, possibly random, initial
vector; only the spectral start is formalized, for every choice of leading eigenvector. Convergence
to the optimum is up to phase, `e^{iθ_t} x_t → x̂`. 'With high probability' is stated for every
noise sequence `0 ≤ σ_n ≤ c √(n / log n)` and all signals `z_n`: the outer measure of the failure
event tends to `0`. Bandeira's 'small enough noise' (in the notes: 'for which values of σ') is fixed
at the scale of Zhong and Boumal.
-/

open MeasureTheory Matrix Complex Filter Topology
open MathlibExt.Probability.AngularSynchronizationShared

/-- The entrywise projection of the power method: `P(a)_k = a_k / |a_k|`, and `1` when `a_k = 0`. -/
noncomputable def phaseProjection {n : ℕ} (a : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if a k = 0 then 1 else a k / (‖a k‖ : ℂ)

/-- The iterates of the projected (generalized) power method from `x₀`: `x_{t+1} = P(C x_t)`. -/
noncomputable def powerIterate {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (x₀ : Fin n → ℂ) :
    ℕ → Fin n → ℂ
  | 0 => x₀
  | t + 1 => phaseProjection (C *ᵥ powerIterate C x₀ t)

/-- `x₀` is a leading eigenvector of the Hermitian matrix `C`, scaled to `‖x₀‖₂ = √n`: it maximizes
the Rayleigh quotient `x* C x` over the vectors with `‖x‖₂² = n`. -/
def IsScaledLeadingEigenvector {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (x₀ : Fin n → ℂ) : Prop :=
  ∑ k, ‖x₀ k‖ ^ 2 = n ∧ ∀ y : Fin n → ℂ, ∑ k, ‖y k‖ ^ 2 = n → quadForm C y ≤ quadForm C x₀

/-- The power method succeeds on `C`: problem (P) has a global maximizer `xhat`, unique up to
phase, and from every scaled leading eigenvector `x₀` the iterates converge to `xhat` up to phase
(`e^{iθ_t} x_t → xhat` for some phases `θ_t`). -/
def PowerMethodSucceeds {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ xhat, IsUniqueOptimumUpToPhase C xhat ∧ ∀ x₀, IsScaledLeadingEigenvector C x₀ →
    ∃ θ : ℕ → ℝ, Tendsto (fun t => exp (θ t * I) • powerIterate C x₀ t) atTop (𝓝 xhat)

/-- Bandeira's Open Problem 10.1, with a positive answer at the noise scale of Zhong and Boumal:
there is `c > 0` such that whenever `0 ≤ σ_n ≤ c √(n / log n)`, for any signals `z_n` the
probability that the projected power method from a leading eigenvector fails to converge to the
optimum of (P), unique up to phase, tends to `0`. -/
def projectedPowerMethodConverges : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (σ : ℕ → ℝ) (z : (n : ℕ) → Fin n → ℂ),
    (∀ n, 0 ≤ σ n ∧ σ n ≤ c * Real.sqrt (n / Real.log n)) → (∀ n, IsPhaseVector (z n)) →
      Tendsto (fun n => noiseMeasure n
        {ω | ¬ PowerMethodSucceeds (measurementMatrix (z n) (σ n) ω)}) atTop (𝓝 0)

/--
Resolved true: Zhong and Boumal (Theorems 6 and 7) prove that for `σ ≤ c₀ √(n / log n)`, with
probability `1 - O(n^{-2})`, the generalized power method started at a leading eigenvector (`‖x₀‖₂ =
√n`) converges linearly, up to phase, to the global optimum of (P), which is unique up to phase;
this answers Bandeira's question for the spectral start and Gaussian noise up to the level `√(n /
log n)`, against the `Õ(√n)` regime seen in experiments. Source: A. S. Bandeira, Ten Lectures and
Forty-Two Open Problems in the Mathematics of Data Science (2015-2016), Section 10.2, Open Problem
10.1, https://afonsobandeira.wordpress.com/2015/12/09/42l10psynchronization/; resolution: Y. Zhong
and N. Boumal, Near-optimal bounds for phase synchronization, SIAM J. Optim. 28 (2018), 989-1016;
arXiv:1703.06605, Theorem 6 (Algorithm 1 converges linearly to some x̂ up to phase: d₂(x_t, x̂) ≤
2^{-t} √n for t = 0, 1, 2, ...) and Theorem 7 (x̂ is the unique optimum of (P) up to phase): there
is an absolute c₀ > 0 such that if σ ≤ c₀ √(n / log n), both hold with probability 1 - O(n^{-2});
Algorithm 1 starts at a leading eigenvector x₀ of C with ‖x₀‖₂ = √n and iterates x_t = P(C x_{t-1});
the noise W is Hermitian with zero diagonal and independent centered sub-gaussian real and imaginary
parts above the diagonal (Section 2), which covers the Gaussian model of Section 1,
https://doi.org/10.1137/17M1122025.
-/
public theorem_wanted projectedPowerMethodConverges_holds : projectedPowerMethodConverges

end MathlibExt.Probability.AngularSynchronizationPowerMethodAMR27Problem1001Wanted
