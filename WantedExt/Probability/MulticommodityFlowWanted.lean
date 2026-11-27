/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.MarkovChainCheeger
public import MathlibExt.Probability.MulticommodityFlow

/-!
# Wanted: rapid mixing yields a low-congestion flow

Sinclair's Theorem 8 states that the resistance is at most `16 τ`. Its key step, Lemma 7,
is proved as `MathlibExt.Probability.Flows.div_eight_le_pow_apply`; what remains is the flow
built from the `2τ`-step trajectories of the chain, with cycles bypassed.

Sinclair concludes from this and Cheeger's inequality (`MathlibExt.Probability.MarkovChainCheeger`),
with Theorems 3, 5 and 5′ (`MathlibExt.Probability.CanonicalPaths` and
`MathlibExt.Probability.MulticommodityFlow`), that a reversible chain mixes rapidly if and only
if it supports a flow of polynomially bounded congestion, if and only if its conductance is at
least an inverse polynomial. The mixing-time estimate also depends on the smallest eigenvalue
(handled, for instance, by making the chain lazy) and on
`log(1/π(x))` for the starting state `x`.

## References

* A. Sinclair, "Improved bounds for mixing rates of Markov chains and multicommodity flow",
  *Combinatorics, Probability and Computing* **1** (1992), 351–370: Theorem 2, Lemma 7,
  Theorem 8.
* A. Sinclair and M. Jerrum, "Approximate counting, uniform generation and rapidly mixing Markov
  chains", *Information and Computation* **82** (1989), 93–133: Lemma 3.3.
-/

@[expose] public section

open Finset Matrix
open MathlibExt.Probability.CanonicalPaths MathlibExt.Probability.MarkovMixing
open MathlibExt.Probability.Flows ProbabilityTheory

namespace MathlibExt.Probability.MulticommodityFlowWanted

/-- **Rapid mixing implies a low-congestion flow** (A. Sinclair, *Combin. Probab. Comput.* 1
(1992), Theorem 8: the resistance satisfies `ρ ≤ 16 τ`). Let `P` be a stochastic matrix
satisfying detailed balance with respect to a probability vector `π > 0`, and suppose every row
of `Pᵗ` is within total variation distance `1/4` of `π` for all `t ≥ τ` (so
`τ ≥ max_x τ_x(1/4)`). Then some multicommodity flow, routing `π(x) π(y)` from `x` to `y` over
simple paths of the chain, puts at most `16 τ · π(u) P(u, v)` on every oriented edge `(u, v)`. -/
theorem_wanted exists_multicommodityFlow_load_le_sixteen_mul {S : Type*} [Fintype S]
    [DecidableEq S] {π : S → ℝ} (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hrev : IsDetailedBalance π P) {τ : ℕ}
    (hτ : ∀ x, ∀ t, τ ≤ t → tvDist (fun y => (P ^ t) x y) π ≤ 1 / 4) :
    ∃ F : MulticommodityFlow π P, ∀ u v, F.load u v ≤ 16 * τ * (π u * P u v)

end MathlibExt.Probability.MulticommodityFlowWanted
