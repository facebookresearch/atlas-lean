/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST CIRCUIT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND28] LONGEST
CIRCUIT (transformation from HAMILTONIAN CIRCUIT);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
Computer Computations*, Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LongestCircuitDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestCircuit

/-!
# LONGEST CIRCUIT is NP-complete

INSTANCE: a graph `G = (V, E)`, a length `l(e) ∈ ℤ⁺` for each `e ∈ E`, and a positive integer
`K`. QUESTION: is there a simple circuit in `G` whose length (the sum of the lengths of its
edges) is `K` or more?

This is the edge-weighted problem; its special case with every length `1`, where the length of
a circuit is its number of edges, is `MetaMathlibExt.Complexity.NPComplete.LongestCycle`. With
unit lengths and `K = |V|` the question is HAMILTONIAN CIRCUIT, Garey and Johnson's
transformation. A simple circuit is Mathlib's `SimpleGraph.Walk.IsCycle` (a closed walk of
length at least three with no repeated vertex other than its endpoints).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LONGEST CIRCUIT is NP-complete.** Source: Garey and Johnson (1979), [ND28]; Karp (1972). -/
public theorem_wanted longestCircuit_npComplete :
    longestCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestCircuitDec

end MetaMathlibExt.Complexity.NPComplete.LongestCircuit
