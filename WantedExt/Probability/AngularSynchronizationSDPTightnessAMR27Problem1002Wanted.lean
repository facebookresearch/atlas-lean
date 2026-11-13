/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tightness of the angular synchronization SDP (Bandeira, Open Problem 10.2)

Bandeira, Ten Lectures and Forty-Two Open Problems, Open Problem 10.2: is the semidefinite
relaxation `max tr(C X)` over `X ⪰ 0` with `X_ii = 1` of angular synchronization tight with high
probability for noise levels `σ` essentially until the solution of angular synchronization no longer
correlates with the ground truth (in the notes: as long as `σ = Õ(n^{1/2})`)?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Probability.AngularSynchronizationShared

@[expose] public section

namespace MathlibExt.Probability.AngularSynchronizationSDPTightnessAMR27Problem1002Wanted

/-!
Source: A. S. Bandeira, Ten Lectures and Forty-Two Open Problems in the Mathematics of Data Science
(2015-2016), Section 10.2, Open Problem 10.2,
https://afonsobandeira.wordpress.com/2015/12/09/42l10psynchronization/. UnsolvedMath record
UM-02801002 (`AMR-027-1002`), dataset ulamai/UnsolvedMath v1.8.0.

The noise model and problem (P) are those of
`WantedExt/Probability/AngularSynchronizationShared.lean`. The relaxation is Zhong-Boumal's (SDP),
`max Re tr(C X)` over Hermitian positive semidefinite `X ∈ ℂ^{n × n}` with `X_kk = 1`; tight means
that it has the unique solution `x̂ x̂*`, with `x̂` the optimum of (P), unique up to phase. 'With
high probability' is stated for every noise sequence `0 ≤ σ_n ≤ c √(n / log n)` and all signals
`z_n`: the outer measure of the failure event tends to `0`. Bandeira's `Õ(n^{1/2})` (the correlation
threshold is `σ ≈ √n`) is formalized at Zhong and Boumal's scale `√(n / log n)`.
-/

open MeasureTheory Matrix Filter Topology
open MathlibExt.Probability.AngularSynchronizationShared
open scoped ComplexOrder

/-- `X` is feasible for the semidefinite relaxation of (P): Hermitian positive semidefinite with
unit diagonal. -/
def IsSDPFeasible {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  X.PosSemidef ∧ ∀ k, X k k = 1

/-- The semidefinite relaxation `max Re tr(C X)` over feasible `X` is tight with a unique solution:
for some `xhat` that is the optimum of (P), unique up to phase, the rank-one matrix `xhat xhat*` is
the only maximizer. -/
def SDPIsTight {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ xhat, IsUniqueOptimumUpToPhase C xhat ∧ ∀ X, IsSDPFeasible X →
    (C * X).trace.re ≤ (C * vecMulVec xhat (star xhat)).trace.re ∧
      ((C * X).trace.re = (C * vecMulVec xhat (star xhat)).trace.re →
        X = vecMulVec xhat (star xhat))

/-- Bandeira's Open Problem 10.2, with a positive answer at the noise scale of Zhong and Boumal:
there is `c > 0` such that whenever `0 ≤ σ_n ≤ c √(n / log n)`, for any signals `z_n` the
probability that the semidefinite relaxation of angular synchronization is not tight (unique
rank-one solution `xhat xhat*`, `xhat` the optimum of (P)) tends to `0`. -/
def angularSynchronizationSDPTight : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (σ : ℕ → ℝ) (z : (n : ℕ) → Fin n → ℂ),
    (∀ n, 0 ≤ σ n ∧ σ n ≤ c * Real.sqrt (n / Real.log n)) → (∀ n, IsPhaseVector (z n)) →
      Tendsto (fun n => noiseMeasure n
        {ω | ¬ SDPIsTight (measurementMatrix (z n) (σ n) ω)}) atTop (𝓝 0)

/--
Resolved true: Zhong and Boumal (Theorem 5) prove that for `σ ≤ c₀ √(n / log n)`, with probability
`1 - O(n^{-2})`, the semidefinite relaxation has the unique solution `x̂ x̂*`, `x̂` being the global
optimum of (P), unique up to phase; they present this as closing the gap between the earlier
`O(n^{1/4})` analyses and the `Õ(n^{1/2})` regime seen in experiments. Source: A. S. Bandeira, Ten
Lectures and Forty-Two Open Problems in the Mathematics of Data Science (2015-2016), Section 10.2,
Open Problem 10.2, https://afonsobandeira.wordpress.com/2015/12/09/42l10psynchronization/;
resolution: Y. Zhong and N. Boumal, Near-optimal bounds for phase synchronization, SIAM J. Optim. 28
(2018), 989-1016; arXiv:1703.06605, Theorem 5 (Theorem 1 of the introduction): there is an absolute
c₀ > 0 such that if σ ≤ c₀ √(n / log n), then with probability 1 - O(n^{-2}) the semidefinite
program (SDP) max trace(CX) subject to diag(X) = 1, X ⪰ 0 admits a unique solution x̂x̂*, where x̂
is the unique global optimum of (P) up to phase; abstract: 'we bridge the gap, by proving SDP is
tight for σ = O(√(n/log n))', https://doi.org/10.1137/17M1122025.
-/
public theorem_wanted angularSynchronizationSDPTight_holds : angularSynchronizationSDPTight

end MathlibExt.Probability.AngularSynchronizationSDPTightnessAMR27Problem1002Wanted
