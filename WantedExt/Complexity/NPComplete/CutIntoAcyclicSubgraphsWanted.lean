/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUT INTO ACYCLIC SUBGRAPHS is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 182-195,
doi:10.1016/0196-6774(82)90018-9, problem [7] CUT INTO ACYCLIC SUBGRAPHS (reference: P. Gács,
"Partitioning a directed graph into two acyclic subgraphs is NP-complete", manuscript (1981);
transformation from 3SAT);
D. Bokal, G. Fijavž, M. Juvan, P. M. Kayll and B. Mohar, "The circular chromatic number of a
digraph", J. Graph Theory 46 (2004), 227-240, doi:10.1002/jgt.20003.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CutIntoAcyclicSubgraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CutIntoAcyclicSubgraphs

/-!
# CUT INTO ACYCLIC SUBGRAPHS is NP-complete

INSTANCE: a directed graph `G = (V, A)`.
QUESTION: is there a partition of `V` into disjoint sets `V₁` and `V₂` such that both `V₁` and
`V₂` induce acyclic subgraphs (ones containing no nontrivial strongly connected components)?
Equivalently, does `G` have dichromatic number at most 2?

Johnson's column, problem [7], credits the result to an unpublished manuscript of Gács (not
available). Bokal, Fijavž, Juvan, Kayll and Mohar (2004) define the chromatic number `χ(D)` of a
digraph as the least `k` such that `V(D)` can be partitioned into `k` acyclic sets, prove
`χ(D) - 1 < χ_c(D) ≤ χ(D)` (Proposition 1.1), and show in their abstract that "It is
NP-complete to decide if a given digraph has `χ_c` at most 2"; by Proposition 1.1,
`χ_c(D) ≤ 2` holds exactly when `χ(D) ≤ 2`, which is the question above. Membership in NP: the
partition is a certificate, and acyclicity of each induced subgraph is checked in polynomial
time.

The digraph has vertices `0, …, n - 1` and is given by its arc list (`(u, v)` is the arc
`u → v`), without loops or repeated arcs; opposite arcs `u → v` and `v → u` may both be
present, and then form a directed cycle of length 2. The partition is a colouring
`c : Fin n → Fin 2` (`V₁` and `V₂` are its two colour classes; a class may be empty, which
matters only for `n ≤ 1`). A set induces an acyclic subgraph exactly when it contains no closed
directed walk of positive length, the shared MathlibExt predicate
`SimpleGraph.IsDirectedCycle` (`MathlibExt.Combinatorics.SimpleGraph.Dichromatic`), the same
monochromatic-cycle condition as `SimpleGraph.DichromaticColorable`: in a loopless digraph, a
nontrivial strongly connected component contains such a walk, and the vertices of such a walk
lie in one nontrivial strongly connected component.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CUT INTO ACYCLIC SUBGRAPHS is NP-complete.** Source: Johnson (1982), problem [7] (Gács);
Bokal, Fijavž, Juvan, Kayll and Mohar (2004). -/
public theorem_wanted cutIntoAcyclicSubgraphs_npComplete :
    cutIntoAcyclicSubgraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cutIntoAcyclicSubgraphsDec

end MetaMathlibExt.Complexity.NPComplete.CutIntoAcyclicSubgraphs
