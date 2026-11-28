/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST DIRECTED CIRCUIT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND28] LONGEST CIRCUIT, p. 213,
comment: "Remains NP-complete if l(e) = 1 for all e ∈ E, as does the corresponding problem for
directed circuits in directed graphs"; problem [GT38] DIRECTED HAMILTONIAN CIRCUIT;
R. M. Karp, "Reducibility among combinatorial problems", in Complexity of Computer
Computations (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LongestDirectedCircuitDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestDirectedCircuit

/-!
# LONGEST DIRECTED CIRCUIT is NP-complete

INSTANCE: a directed graph `G = (V, A)`, a length `l(a) ∈ ℤ⁺` for each `a ∈ A`, and a positive
integer `K`. QUESTION: is there a simple directed circuit in `G` of length `K` or more, i.e.,
whose arc lengths sum to at least `K`?

This is LONGEST CIRCUIT (`MetaMathlibExt.Complexity.NPComplete.LongestCircuit`) for directed
circuits in directed graphs. The vertices are `Fin n`; the arcs are listed with their lengths
(an entry `(u, v, l)` is the arc `u → v` of length `l`), with no loops and no two entries for
the same ordered pair, so `u → v` and `v → u` may both be arcs. The graph is a
`Cslib.Algorithms.Lean.DirectedAdjacency`, and a simple directed circuit is CSLib's
`TopologicalSort.DirectedCycleIn`: a nonempty list of distinct vertices, each joined to the
next by an arc, with an arc from the last back to the first (without loops, it has at least
two vertices). Its length is `DirectedAdjacency.pathWeight` of the arc lengths along the
circuit closed up by repeating its first vertex.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LONGEST DIRECTED CIRCUIT is NP-complete.** Source: Garey and Johnson (1979), [ND28],
comment; Karp (1972), DIRECTED HAMILTONIAN CIRCUIT. -/
public theorem_wanted longestDirectedCircuit_npComplete :
    longestDirectedCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestDirectedCircuitDec

end MetaMathlibExt.Complexity.NPComplete.LongestDirectedCircuit
