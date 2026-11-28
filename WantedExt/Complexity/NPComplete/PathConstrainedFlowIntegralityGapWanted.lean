/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH CONSTRAINED NETWORK FLOW without an integrality gap is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND34] PATH CONSTRAINED NETWORK FLOW
(p. 215), comment "The corresponding problem with non-integral flows is equivalent to LINEAR
PROGRAMMING, but the question of whether the best rational flow fails to exceed the best integral
flow is NP-complete" (credited there to H. J. Prömel, 1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathConstrainedFlowIntegralityGapDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathConstrainedFlowIntegralityGap

open MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlow
  (PathConstrainedNetworkFlowInstance capacity pathFlow)
open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted (IsFeasibleFlow)

/-!
# PATH CONSTRAINED NETWORK FLOW without an integrality gap is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, a capacity
`c(a) ∈ ℤ⁺` for each `a ∈ A`, and a collection `P` of directed paths in `G`.
QUESTION: does the best rational flow fail to exceed the best integral flow? That is, writing a
flow as `g : P → ℚ₀⁺` (rational) or `g : P → ℤ₀⁺` (integral) with induced arc flow
`f(a) = ∑_{p ∈ P(a)} g(p)` within the capacities and conserved at every `v ∈ V - {s, t}`, is the
largest net flow into `t` of a rational flow at most the largest net flow into `t` of an integral
flow?

This is Garey and Johnson's integrality question for PATH CONSTRAINED NETWORK FLOW ([ND34],
`PathConstrainedNetworkFlowWanted`). The instance is the parent's without the requirement `R`,
which the question does not use; `toParent` restores it as `R = 1` so that
`PathConstrainedNetworkFlow.WellFormed` applies (a directed graph on `0, ..., n - 1` with positive
capacities, distinct vertices `s` and `t`, every member of `P` a directed path in `G`). Flows are
the parent's: `PathConstrainedNetworkFlow.pathFlow` on rational or natural amounts, and
MathlibExt's `IsFeasibleFlow` for `PathConstrainedNetworkFlow.capacity`.

Both maxima exist (the value of a flow is bounded by the capacities, the rational maximum is the
optimum of a linear program with rational data, and the integral flows take finitely many
values), so "the best rational flow fails to exceed the best integral flow" holds exactly when
some integral flow is at least as large as every rational flow (`NoIntegralityGapFeasible`).
Garey and Johnson call the rational problem equivalent to LINEAR PROGRAMMING; the complementary
question (does the best rational flow exceed the best integral one?) is coNP-complete.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Whether the best rational path-constrained flow fails to exceed the best integral one is
NP-complete.** Source: Garey and Johnson (1979), [ND34], comment (Prömel, 1978). -/
public theorem_wanted pathConstrainedFlowIntegralityGap_npComplete :
    pathConstrainedFlowIntegralityGapDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathConstrainedFlowIntegralityGapDec

end MetaMathlibExt.Complexity.NPComplete.PathConstrainedFlowIntegralityGap
