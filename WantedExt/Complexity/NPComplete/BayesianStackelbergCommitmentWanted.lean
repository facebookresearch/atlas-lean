/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL MIXED STRATEGY TO COMMIT TO in two-player Bayesian games is NP-complete

Source:
V. Conitzer and T. Sandholm, "Computing the optimal strategy to commit to", Proceedings of the
7th ACM Conference on Electronic Commerce (EC 2006), 82-90, doi:10.1145/1134707.1134717,
Sections 2.1, 3.1, Theorem 7 (NP-hardness), and the linear programs in the proofs of Theorems 2
and 8 (adapted below for membership in NP).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BayesianStackelbergCommitmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BayesianStackelbergCommitment

/-!
# OPTIMAL MIXED STRATEGY TO COMMIT TO in two-player Bayesian games is NP-complete

A two-player Bayesian game between a leader with a single type and a follower: the leader has
actions `S`, the follower has actions `T` and a set of types `Θ` with a probability
distribution `π`; the leader's utility is `u_l(s, t)` and the follower's utility in type `θ` is
`u_f^θ(s, t)`. The leader commits to a mixed strategy `p ∈ Δ(S)`; each follower type `θ` plays
a best response to `p`, breaking ties in the leader's favor. Conitzer and Sandholm (2006),
Theorem 7: finding an optimal mixed strategy to commit to in 2-player Bayesian games is
NP-hard, even when the leader has only a single type and the follower has only two actions;
their proof shows that deciding whether the optimal strategy gives the leader expected utility
at least a given threshold is NP-hard. The decision problem stated here: given the game and a
threshold `k`, is there `p ∈ Δ(S)` whose leader expected utility, against the follower's
leader-favorable best responses, is at least `k`? Theorem 7 gives NP-hardness of this threshold
version. Membership in NP is not stated in the paper; it follows from the linear programs in the
proofs of their Theorems 2 and 8, adapted to several follower types: guess a pure follower
strategy `t : Θ → T`; the largest leader expected utility over mixed strategies under which every
`t θ` is a best response of type `θ` is the optimum of a linear program of polynomial size, and
the instance is a yes-instance iff that optimum is at least `k` for some `t`.

Since the leader's utility for each follower type depends only on that type's action, the
leader-favorable best responses reach `k` iff some choice `t : Θ → T` of best responses
(one per type) reaches `k`; `BayesianStackelbergCommitmentFeasible` states the question in
this form.

Utilities are integers, each encoded as a `(positive part, negative part)` pair as in
`ZeroOneILPWanted`; the prior is given by natural-number weights (`π θ = w θ / ∑ w`); the
threshold is a rational `(a - b) / d` with `d > 0`. Scaling the leader's utilities and `k` by a
common positive factor, or one follower type's utilities by a positive factor, changes neither
best responses nor the answer, so rational utilities reduce to integer ones.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **The threshold decision version of OPTIMAL MIXED STRATEGY TO COMMIT TO in two-player
Bayesian games is NP-complete.** NP-hardness: Conitzer and Sandholm (2006), Theorem 7; membership
in NP: one linear program per guessed pure follower strategy, adapted from their Theorems 2 and 8
(see the module docstring). -/
public theorem_wanted bayesianStackelbergCommitment_npComplete :
    bayesianStackelbergCommitmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bayesianStackelbergCommitmentDec

end MetaMathlibExt.Complexity.NPComplete.BayesianStackelbergCommitment
