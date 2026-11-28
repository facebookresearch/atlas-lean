/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNDIRECTED FLOW WITH LOWER BOUNDS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND37] UNDIRECTED FLOW
WITH LOWER BOUNDS;
A. Itai, "Two-commodity flow", Journal of the ACM 25 (1978), 596-611,
doi:10.1145/322092.322100.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBounds

/-!
# UNDIRECTED FLOW WITH LOWER BOUNDS is NP-complete

INSTANCE: a graph `G = (V, E)`, specified vertices `s` and `t`, a capacity `c(e) ∈ ℤ⁺` and a
lower bound `l(e) ∈ ℤ₀⁺` with `l(e) ≤ c(e)` for each `e ∈ E`, and a requirement `R ∈ ℤ⁺`.
QUESTION: is there a flow function `f : {(u, v), (v, u) : {u, v} ∈ E} → ℤ₀⁺` such that for each
`{u, v} ∈ E` either `f(u, v) = 0` or `f(v, u) = 0`,
`l({u, v}) ≤ max (f(u, v), f(v, u)) ≤ c({u, v})`, flow is conserved at every vertex other than
`s` and `t`, and the net flow into `t` is at least `R`?

The vertices are `0, ..., n - 1`. Each edge is a record `(u, v, l, c)`: the edge `{u, v}` with
lower bound `l` and capacity `c`; there are no self-loops and at most one record per unordered
pair. A flow is a function `f : Fin n → Fin n → ℕ` (integral and nonnegative) on ordered
pairs; it is checked with `IsFeasibleFlow` from `MathlibExt.Combinatorics.Graph.MaxFlowMinCut`
against the symmetric capacity `capacity`, which is `c({u, v})` on both orientations of an edge
and `0` elsewhere. So `f` vanishes off the two orientations of the edges, `f(u, v) ≤ c({u, v})`
and `f(v, u) ≤ c({u, v})` (that is, `max (f(u, v), f(v, u)) ≤ c({u, v})`), and flow is
conserved at every vertex other than `s` and `t`. The remaining edge conditions (one direction
carries no flow, and the larger direction meets the lower bound) and the requirement on the net
flow into `t` are stated directly.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/-- **UNDIRECTED FLOW WITH LOWER BOUNDS is NP-complete.** Source: Garey and Johnson (1979),
[ND37]; Itai (1978). -/
public theorem_wanted undirectedFlowWithLowerBounds_npComplete :
    undirectedFlowWithLowerBoundsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L undirectedFlowWithLowerBoundsDec

end MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBounds
