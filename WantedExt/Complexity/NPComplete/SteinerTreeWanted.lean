/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), STEINER TREE IN GRAPHS;
R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTree

/-!
# STEINER TREE is NP-complete

An undirected weighted graph, a list of terminals, and a budget `K`. The question is whether
some sublist of edges of total weight at most `K` connects all terminals. Weights are positive,
and there is at most one weighted edge per unordered vertex pair, so the edge list is a
weighted simple graph. A connecting edge set contains a tree of no greater weight, so
acyclicity need not be stated separately.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STEINER TREE is NP-complete.** The decision problem STEINER TREE belongs to NP, and every
decision problem in NP reduces to STEINER TREE by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), STEINER TREE IN GRAPHS; R. M. Karp, "Reducibility among
combinatorial problems" (1972). -/
public theorem_wanted steinerTree_npComplete :
    steinerTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTree
