/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.PengCentralLimitTheorem
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Wanted: Peng's law of large numbers under sublinear expectations

In a sublinear expectation space, i.i.d. means: `Y_{i+1} =ᵈ Y_i` and `Y_{i+1}` is independent
from `(Y_1, …, Y_i)`, in the one-sided sense of
`MathlibExt.Probability.SublinearExpectation.SublinearExpectationSpace.IndepFrom`. Peng's limit
theorems say that the sample mean converges in law to a *maximal distribution* (the whole interval
of means `[μ_, μ̄]`, not a point) and that the normalised sum of a mean-certain sequence converges
in law to the *G-normal distribution* (S. Peng, *Nonlinear Expectations and Stochastic Calculus
under Uncertainty*, arXiv:1002.4546v1, 2010, Chapter II, Theorems 3.1 and 3.3; S. Peng, Proc. ICM
2010, Vol. I, Theorem 2.4 and Corollary 2.5). This module states the law of large numbers, `lln`,
in dimension one and for Lipschitz test functions (Peng allows every continuous function of linear
growth, through the completion of `H`). The central limit theorem, `clt`, in the same setting
lives in `MathlibExt.Probability.PengCentralLimitTheorem`, which this module imports publicly.

The hypotheses of both theorems are satisfiable with genuine uncertainty (`μ_ < μ̄`, `σ_ < σ̄`):
Peng, arXiv:1002.4546v1, Chapter II, Proposition 1.7 constructs a G-normal random variable for
every admissible `G`, and the product spaces of Chapter I, Proposition 3.15 carry i.i.d. sequences.
The tests for these theorems exhibit only zero-variance witnesses under Dirac expectations.

## References

* S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*, arXiv:1002.4546v1,
  2010 (published by Springer, 2019), Chapter II, §3.
* S. Peng, *A new central limit theorem under sublinear expectations*, arXiv:0803.2656, 2008,
  Theorem 5.1.
-/

@[expose] public section

open Filter Topology Finset
open MathlibExt.Probability.SublinearExpectation

namespace MathlibExt.Probability.SublinearExpectation.PengLimitTheoremsWanted

/-- **Peng's law of large numbers under a sublinear expectation** (one-dimensional). Let
`(Y_i)` be real random variables in a sublinear expectation space with `Y_{i+1} =ᵈ Y_i` and
`Y_{i+1}` independent from `(Y_0, …, Y_i)`. Then for every Lipschitz `φ`,
`E[φ((Y_0 + ⋯ + Y_{n-1}) / n)] → max_{μ_ ≤ y ≤ μ̄} φ(y)`, where `μ̄ = E[Y_0]` and
`μ_ = -E[-Y_0]`: the sample mean converges in law to the maximal distribution on `[μ_, μ̄]`.
S. Peng, arXiv:1002.4546v1, Chapter II, Theorem 3.1 with `d = 1`, in the form of Remark 3.2. -/
theorem_wanted lln {Ω : Type*} (S : SublinearExpectationSpace Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, Y i ∈ S.H)
    (hid : ∀ i, SublinearExpectationSpace.IdentDistrib S S (Y (i + 1)) (Y i))
    (hind : ∀ i, S.IndepFrom (Y (i + 1)) (fun ω (j : Fin (i + 1)) ↦ Y j ω))
    {φ : ℝ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) :
    Tendsto (fun n : ℕ ↦ S.E (fun ω ↦ φ ((∑ i ∈ range n, Y i ω) / n))) atTop
      (𝓝 (sSup (φ '' Set.Icc (-S.E (fun ω ↦ -Y 0 ω)) (S.E (Y 0)))))

end MathlibExt.Probability.SublinearExpectation.PengLimitTheoremsWanted
