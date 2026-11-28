/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST DIRECTED PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND29] LONGEST PATH, p. 213,
comment: "Remains NP-complete if l(e) = 1 for all e ∈ E, as does the corresponding problem for
directed paths in directed graphs"; problems [GT38] DIRECTED HAMILTONIAN CIRCUIT and [GT39]
HAMILTONIAN PATH (directed variant);
R. M. Karp, "Reducibility among combinatorial problems", in Complexity of Computer
Computations (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LongestDirectedPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestDirectedPath

/-!
# LONGEST DIRECTED PATH is NP-complete

INSTANCE: a directed graph `G = (V, A)`, a length `l(a) ∈ ℤ⁺` for each `a ∈ A`, a positive
integer `K`, and specified vertices `s, t ∈ V`. QUESTION: is there a simple directed path in
`G` from `s` to `t` of length `K` or more, i.e., whose arc lengths sum to at least `K`?

This is LONGEST PATH (Garey and Johnson [ND29]) for directed paths in directed graphs. The
vertices are `Fin n`; the arcs are listed with their lengths (an entry `(u, v, l)` is the arc
`u → v` of length `l`), with no loops and no two entries for the same ordered pair. The graph is
a `Cslib.Algorithms.Lean.DirectedAdjacency`. A directed path from `s` to `t` is a
`List.IsChainFromTo` chain of arcs from `s` to `t` (a nonempty vertex list starting at `s`,
ending at `t`, each vertex joined to the next by an arc), and it is simple when its vertices
are distinct. Its length is `DirectedAdjacency.pathWeight` of the arc lengths, the measure of
CSLib's Dijkstra specification.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LONGEST DIRECTED PATH is NP-complete.** Source: Garey and Johnson (1979), [ND29],
comment; Karp (1972), DIRECTED HAMILTONIAN CIRCUIT. -/
public theorem_wanted longestDirectedPath_npComplete :
    longestDirectedPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestDirectedPathDec

end MetaMathlibExt.Complexity.NPComplete.LongestDirectedPath
