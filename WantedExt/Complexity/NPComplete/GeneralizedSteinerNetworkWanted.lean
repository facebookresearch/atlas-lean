/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED STEINER NETWORK is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM GENERALIZED STEINER NETWORK ("Also called Minimum Survivable Network");
K. Jain, "A factor 2 approximation algorithm for the generalized Steiner network problem",
Combinatorica 21 (2001), 39-60, doi:10.1007/s004930170004 (the problem with a bound `u_e` on
the number of copies of each edge `e`);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (STEINER TREE is NP-complete);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeneralizedSteinerNetworkDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedSteinerNetwork

/-!
# GENERALIZED STEINER NETWORK is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight function `w : E → ℕ`, a capacity function
`c : E → ℕ`, a requirement function `r : V × V → ℕ`, and a positive integer `K`.
QUESTION: is there a function `f : E → ℕ` such that `f(e) ≤ c(e)` for each edge `e`, such that
for any pair of nodes `i` and `j` the number of edge-disjoint paths between `i` and `j` is at
least `r(i, j)` when `f(e)` copies of each edge `e` are available, and such that the cost
`∑_{e ∈ E} w(e) f(e)` is at most `K`?

This is the decision version of MINIMUM GENERALIZED STEINER NETWORK in the Crescenzi-Kann
compendium, whose solution is, verbatim, "A Steiner network over G that satisfies all the
requirements and obeys all the capacities, i.e., a function f : E → N such that, for each edge
e, f(e) ≤ c(e) and, for any pair of nodes i and j, the number of edge disjoint paths between i
and j is at least r(i,j) where, for each edge e, f(e) copies of e are available", with measure
`∑_{e ∈ E} w(e) f(e)`. The capacity `c(e)` is the bound `u_e` on the number of copies of `e`
in Jain's formulation of the generalized Steiner network (survivable network design) problem.
With every capacity `1` a solution is a subgraph of `G` (each edge used at most once); with
moreover requirements `r(i, j) = 1` for pairs of terminals and `0` otherwise, a feasible `f` is
the indicator of an edge set connecting all terminals, so the problem contains STEINER TREE IN
GRAPHS ([ND12], NP-complete by Karp (1972)). Capacities are
in binary; a certificate `f` with `f ≤ c` has polynomial size, and each requirement can be
checked by a maximum-flow computation.

Paths in the multigraph with `f(e)` copies of each edge `e` are edge-disjoint exactly when, as
paths of `G`, every edge `e` lies on at most `f(e)` of them (distinct paths through `e` use
distinct copies). So a requirement `r(i, j)` asks for `r(i, j)` paths of `G` (Mathlib's
`SimpleGraph.Path`, possibly repeated) from `i` to `j` such that every edge `e` lies on at most
`f(e)` of them. With `f(e) = 1` for all `e` this is MathlibExt's
`MengerEdgeWanted.IsEdgeDisjointSTPaths` (distinct paths share no edge).

The graph is given as a list of edges `(u, v, w, c)` with endpoints, weight and capacity, at
most one entry per unordered pair; `f` is indexed by the entries of this list. The requirement
function is given as a list of triples `(i, j, r(i, j))` with `i ≠ j`, at most one per ordered
pair; pairs not listed, in particular every pair `(i, i)`, have requirement `0` (a path from a
node to itself has no edges, so a requirement on `(i, i)` would be met by any `f`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED STEINER NETWORK is NP-complete.** Source: Crescenzi and Kann, MINIMUM GENERALIZED
STEINER NETWORK; Jain (2001); Karp (1972); Garey and Johnson (1979), [ND12]. -/
public theorem_wanted generalizedSteinerNetwork_npComplete :
    generalizedSteinerNetworkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L generalizedSteinerNetworkDec

end MetaMathlibExt.Complexity.NPComplete.GeneralizedSteinerNetwork
