/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH CONSTRAINED NETWORK FLOW is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND34] PATH CONSTRAINED NETWORK FLOW
(p. 215; credited there to H. J. Prömel, 1978; transformation from 3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathConstrainedNetworkFlowDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlow

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted (IsFeasibleFlow)

/-!
# PATH CONSTRAINED NETWORK FLOW is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, a capacity
`c(a) ∈ ℤ⁺` for each `a ∈ A`, a collection `P` of directed paths in `G`, and a requirement
`R ∈ ℤ⁺`.
QUESTION: is there a function `g : P → ℤ₀⁺` such that if `f : A → ℤ₀⁺` is the flow function
defined by `f(a) = ∑_{p ∈ P(a)} g(p)`, where `P(a) ⊆ P` is the set of all paths in `P` containing
the arc `a`, then `f` is such that (1) `f(a) ≤ c(a)` for all `a ∈ A`, (2) for each
`v ∈ V - {s, t}`, flow is conserved at `v`, and (3) the net flow into `t` is at least `R`?

Vertices are `0, ..., n - 1`, arcs are listed as `(tail, head, capacity)`, and each path of `P`
is a list of vertices, a directed path in `G` in the sense of
`DirectedTwoDisjointConnectingPaths.IsDirectedPath` (distinct vertices, an arc from each vertex
to the next); its arcs are its consecutive vertex pairs. The paths need not start at `s` or end at
`t`. `g` is indexed by position in `P`, and `pathFlow i g u v` is the induced flow on `(u, v)`.
Conditions (1) and (2) are MathlibExt's `IsFeasibleFlow` for the capacity `capacity i u v` (`0`
off the arcs), as in `DirectedTwoCommodityIntegralFlowWanted`. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PATH CONSTRAINED NETWORK FLOW is NP-complete.** Source: Garey and Johnson (1979), [ND34]
(Prömel, 1978). -/
public theorem_wanted pathConstrainedNetworkFlow_npComplete :
    pathConstrainedNetworkFlowDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathConstrainedNetworkFlowDec

end MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlow
