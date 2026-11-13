/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Relative age in null recurrent renewal processes (Thorisson, Problem 1.1)

H. Thorisson, Some Open Probability Problems, Problem 1.1: let `S_n = S_0 + X_1 + ⋯ + X_n` be a
renewal process with i.i.d. strictly positive non-lattice recurrence times of infinite mean (null
recurrent), `A_t` the age, `B_t` the residual life, `D_t = A_t + B_t` and `U_t = A_t / D_t`. Does
`U_t` still tend in distribution to a uniform random variable on `[0, 1]` as `t → ∞` (as it does in
the positive recurrent case)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.IdentDistrib

@[expose] public section

namespace MathlibExt.Probability.NullRecurrentRenewalRelativeAgeAMR98Problem0001Wanted

/-!
Source: H. Thorisson, Some Open Probability Problems, Problem 1.1. UnsolvedMath record UM-09900001
(`AMR-098-0001`), dataset ulamai/UnsolvedMath v1.8.0.

The claim refuted is the universal one, for zero-delay processes (`S_0 = 0`), a special case of
Thorisson's setting, so its failure answers the question. `X 0, X 1, …` are i.i.d. (Mathlib
`iIndepFun` plus `IdentDistrib`), strictly positive, non-lattice (`P(X ∈ dℤ) < 1` for every `d > 0`,
Thorisson's definition) with `E X = ∞`. With `S n = X 0 + ⋯ + X (n - 1)`, the event `{U_t ≤ u}` is
that `t` lies in a cycle `[S n, S (n + 1))` (of length `X n = D_t`) with `t - S n = A_t ≤ u X n`.
Convergence in distribution to the uniform law is `P(U_t ≤ u) → u` for every `u ∈ [0, 1]` (the
uniform distribution function is continuous).
-/

/-- The renewal epochs `S n = X 0 + ⋯ + X (n - 1)` (`S 0 = 0`, no delay). -/
def renewalEpoch {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

/-- The event `{U_t ≤ u}`: `t` lies in the cycle `[S n, S (n + 1))` of length `X n` and the relative
age `A_t / D_t = (t - S n) / X n` is at most `u`. -/
def relativeAgeLE {Ω : Type*} (X : ℕ → Ω → ℝ) (t u : ℝ) : Set Ω :=
  {ω | ∃ n, renewalEpoch X n ω ≤ t ∧ t < renewalEpoch X (n + 1) ω ∧
    t - renewalEpoch X n ω ≤ u * X n ω}

/-- Thorisson's Problem 1.1 (Some Open Probability Problems): for every null recurrent renewal
process (i.i.d. strictly positive non-lattice recurrence times with infinite mean), the relative
age `U_t = A_t / D_t` tends in distribution to the uniform law on `[0, 1]`, i.e.
`P(U_t ≤ u) → u` for every `u ∈ [0, 1]`. -/
def nullRecurrentRelativeAgeUniform : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (X : ℕ → Ω → ℝ), (∀ i, Measurable (X i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P P) → (∀ i ω, 0 < X i ω) →
    (∀ d : ℝ, 0 < d → P {ω | ∃ k : ℤ, X 0 ω = k * d} < 1) →
    ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂P = ⊤ →
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun t : ℝ => P (relativeAgeLE X t u)) Filter.atTop (nhds (ENNReal.ofReal u))

/--
Resolved false: for i.i.d. non-lattice recurrence times with regularly varying tail of index `-α`,
`0 < α < 1` (e.g. Pareto), `A_t / D_t` converges in distribution to `U^{1/α}`, whose distribution
function `u^α` is not uniform (Blanchet–Glynn–Thorisson, Theorem 1; Angus–Ding in full generality).
Source: H. Thorisson, Some Open Probability Problems, Problem 1.1; resolution: J. Angus and Y. Ding,
On the ratio of current age to total life for null recurrent renewal processes, Statist. Probab.
Lett. (2020), https://www.sciencedirect.com/science/article/pii/S0167715220300481; first found by J.
Blanchet, P. Glynn and H. Thorisson, On the limiting ratio of current age to total life for null
recurrent renewal processes, arXiv:1503.08374, Angus-Ding, main results and Concluding remarks: if
the inter-arrival survival function is regularly varying with exponent -α, 0 ≤ α ≤ 1, and the mean
is infinite, then A(t)/C(t) ⇒ U^{1/α} with U uniform (lattice or not), "a definitive answer to the
problem posed in Thorisson (2011)"; Blanchet-Glynn-Thorisson, Theorem 1 (non-arithmetic, regularly
varying density, α ∈ (0, 1)), https://arxiv.org/abs/1503.08374.
-/
public theorem_wanted nullRecurrentRelativeAgeUniform_refuted : ¬ nullRecurrentRelativeAgeUniform

end MathlibExt.Probability.NullRecurrentRenewalRelativeAgeAMR98Problem0001Wanted
