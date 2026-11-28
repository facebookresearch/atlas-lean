/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on K_3,3-free graphs is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4 (Table 1, column "K3,3-free": INDEPENDENT SET
NP-complete, citing Garey and Johnson (1979));
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021
(the same entry, unchanged);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET (comment: remains
NP-complete for cubic planar graphs);
K. Kuratowski, "Sur le problème des courbes gauches en topologie", Fundamenta Mathematicae 15
(1930), 271-283 (a planar graph has no subgraph homeomorphic to `K_3,3`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IndependentSetK33FreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetK33Free

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-!
# INDEPENDENT SET on K_3,3-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` with no subgraph homeomorphic to `K_3,3`, and a positive integer
`K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) on Johnson's class "K3,3-free graphs" (graphs with no subgraph
homeomorphic to `K_3,3`). A subgraph homeomorphic to `K_3,3` is a subdivision of `K_3,3` inside
`G`: six distinct branch vertices `a_0, a_1, a_2, b_0, b_1, b_2` and, for every `i` and `j`, a
path from `a_i` to `b_j`, where the inner vertices of a path are not branch vertices and no two
of the nine paths share an inner vertex. `HasK33Subdivision G` states this with the branch
vertices given by an injective map `Fin 3 ⊕ Fin 3 → V` and Mathlib paths (`Walk.IsPath`); the
inner vertices of a walk are its support without the first and last vertex
(`support.tail.dropLast`), and two different paths are `SimpleGraph.InternallyDisjoint`
(`MathlibExt.Combinatorics.SimpleGraph.Connectivity`: their inner vertex lists are disjoint).

The instance type (vertex count `n`, edge list, bound `K`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (a `Finset` of at least `K`
vertices whose coercion is Mathlib's `SimpleGraph.IsIndepSet`) are those of the edge-list
INDEPENDENT SET statement on `main`,
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`, whose triangle-free
restriction lives only in its `WellFormed`, which this module does not use. `WellFormed` here
asks for a simple edge list on `Fin n`, `0 < K ≤ |V|` ([GT20]'s instance class), and the class.

Garey and Johnson record INDEPENDENT SET as NP-complete on cubic planar graphs; by Kuratowski's
theorem a planar graph has no subgraph homeomorphic to `K_3,3`, so those instances are instances
of this problem with the same answer. Johnson's table lists the problem as NP-complete on this
class for that reason.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDEPENDENT SET on `K_3,3`-free graphs is NP-complete.** Source: Johnson (1985), Table 1;
de Figueiredo, de Melo, Sasaki and Silva (2022); Garey and Johnson (1979), [GT20], comment;
Kuratowski (1930). -/
public theorem_wanted independentSetK33Free_npComplete :
    independentSetK33FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetK33FreeDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetK33Free
