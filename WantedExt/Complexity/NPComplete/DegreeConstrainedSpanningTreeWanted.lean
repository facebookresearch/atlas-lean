/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEGREE-CONSTRAINED SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), DEGREE-CONSTRAINED
SPANNING TREE (the `K = 2` slice is Hamiltonian path).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DegreeConstrainedSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSpanningTree

/-!
# DEGREE-CONSTRAINED SPANNING TREE is NP-complete

An undirected graph and a bound `K`. The question is whether the graph has a spanning tree
whose maximum degree is at most `K`. A connected edge set with `n - 1` edges is a tree, so
acyclicity need not be stated separately; the degree bound is stated by forbidding `K + 1`
incident edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DEGREE-CONSTRAINED SPANNING TREE is NP-complete.** The decision problem
DEGREE-CONSTRAINED SPANNING TREE belongs to the class NP, and every decision problem in NP has a
polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), DEGREE-CONSTRAINED SPANNING TREE (the `K =
2` slice is Hamiltonian path). -/
public theorem_wanted degreeConstrainedSpanningTree_npComplete :
    degreeConstrainedSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L degreeConstrainedSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSpanningTree
