/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZERO FORCING NUMBER is NP-complete

Source:
S. Fallat, K. Meagher and B. Yang, "On the complexity of the positive semidefinite zero forcing
number", Linear Algebra and its Applications 491 (2016), 101-122,
doi:10.1016/j.laa.2015.03.011, Corollary 3.4 (via B. Yang, "Fast-mixed searching and related
problems on graphs", Theoretical Computer Science 507 (2013), 100-113,
doi:10.1016/j.tcs.2013.04.015);
A. Aazami, *Hardness results and approximation algorithms for some problems on graphs*, PhD
thesis, University of Waterloo (2008), Theorem 2.3.1 (NP-hardness with node weights 0 and 1, on
planar graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ZeroForcingNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ZeroForcingNumber

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# ZERO FORCING NUMBER is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` and a nonnegative integer `K`.
QUESTION: is there a set `S ⊆ V` with `|S| ≤ K` that is a zero forcing set of `G`, that is, if
the vertices of `S` are colored black and all others white, repeatedly applying the color-change
rule "a black vertex with exactly one white neighbor turns that neighbor black" makes every
vertex black? Equivalently, is the zero forcing number `Z(G)` at most `K`?

The final set of black vertices does not depend on the order in which the rule is applied: it
is the least set containing `S` that is closed under the rule "if `u` is black, `v` is a
neighbor of `u`, and every neighbor of `u` other than `v` is black, then `v` is black" (the
process stops exactly when this set is reached, and each step stays inside any such closed
set). `Forced G S` is that least set, as an inductive predicate.

The instance type (vertex count `n`, edge list, bound `K`), the graph (`GraphColoring.Graph`,
the edge-list graph on `Fin n`) and the simple-edge-list condition (`GraphColoring.WellFormed`)
are reused from `GraphColoringWanted`; the simple-edge-list condition is the whole
well-formedness. `K` ranges over all natural numbers, as the nonnegative
integer `k` in Fallat, Meagher and Yang's Corollary 3.4: `K = 0` is a yes-instance exactly for
the graph with no vertices, and `K ≥ |V|` is always a yes-instance (`S = V`).

Fallat, Meagher and Yang prove that the fast-mixed search number of a graph equals its zero
forcing number (Theorem 3.1) and derive from Yang's results on fast-mixed searching their
Corollary 3.4: "Given a graph `G` and a nonnegative integer `k`, it is NP-complete to determine
whether `Z(G) ≤ k`. This problem remains NP-complete even for 2-connected (biconnected) graphs
with maximum degree 4." Aazami had earlier proved the problem (as the Propagation problem)
NP-hard on planar graphs with node weights 0 and 1. Membership in NP: the closure of `S` is
computed in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ZERO FORCING NUMBER is NP-complete.** Source: Fallat, Meagher and Yang (2016),
Corollary 3.4; Yang (2013); Aazami (2008). -/
public theorem_wanted zeroForcingNumber_npComplete :
    zeroForcingNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L zeroForcingNumberDec

end MetaMathlibExt.Complexity.NPComplete.ZeroForcingNumber
