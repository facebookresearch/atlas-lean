/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B₁-CPG GRAPH RECOGNITION is NP-complete

Source:
N. Champseix, E. Galby, A. Munaro and B. Ries, "CPG graphs: Some structural and hardness
results", Discrete Applied Mathematics 290 (2021), 17-35, doi:10.1016/j.dam.2020.11.018
(arXiv:1903.01805; Section 1: the definition of CPG and `B_k`-CPG graphs; Theorem 9:
"Recognition is NP-complete in `B_k`-CPG for any `k ≥ 1`");
ISGCI (https://www.graphclasses.org/classes/gc_1338.html), class B_1-CPG, problem "Recognition":
NP-complete, citing Champseix, Galby, Munaro and Ries.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BOneCPGRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BOneCPGRecognition

open CliqueBOneVPG (BendPath pathPoints)
open PartitionIntoCliquesBZeroCPG (double)

/-!
# B₁-CPG GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` a `B₁`-CPG graph, i.e., the contact graph of a
family of pairwise interiorly disjoint paths on a grid, each with at most one bend?

Champseix, Galby, Munaro and Ries (Section 1): "a graph `G = (V, E)` is a CPG graph if there
exists a collection `P` of pairwise interiorly disjoint paths on a grid `G` in one-to-one
correspondence with `V` such that two vertices are adjacent if and only if the corresponding paths
touch. If every such path has at most `k` bends, for some `k ≥ 0`, then the graph is `B_k`-CPG."
Two paths "touch if [they] have a common grid-point", and "an interior point of a path `P` is a
point belonging to `P` and different from its endpoints". Theorem 9 proves recognition
NP-complete for every `k ≥ 1`; membership in NP is witnessed by the endpoints and bend points of
the paths. This module states the case `k = 1` (ISGCI `gc_1338`).

A path with at most one bend is given by its endpoints `a`, `b` and its corner `c`, as the grid
paths of `CliqueBOneVPGWanted` (`BendPath`, with grid points `pathPoints`, those of the legs
`a`-`c` and `c`-`b`); here, as in the CPG model, it is a genuine path from `a` to `b`: the first
leg is horizontal and the second vertical, or the other way round (a leg may have length `0`, so
straight paths are included), and `a ≠ b`, so the path has at least one grid edge. Being
perpendicular, the two legs meet only at `c`, and a bend at `c` exists exactly when both legs have
positive length. Interiorly disjoint paths have no common interior point (so paths of distinct
vertices, each with at least one grid edge, are distinct, as the correspondence requires). As in
`PartitionIntoCliquesBZeroCPGWanted`, interior points are tested on the grid refined by a factor
of `2` (`double`): the points of the refined grid on the doubled path, other than the doubled
endpoints. Two such paths have a common interior point in the plane exactly when they have one on
the refined grid: an isolated common point is the crossing of a horizontal and a vertical leg, at
a grid point, and a common piece of positive length contains the midpoint of a grid edge, which
is no endpoint. Two such paths have a common point exactly when they have a common grid point
(corners and endpoints lie on the grid). Every finite representation can be moved to the grid
`ℕ × ℕ` by replacing coordinates by their ranks, so the class does not depend on these choices.
The paths are not part of the input.

The graph is simple and given by an edge list on `Fin n`. Isolated vertices do not change the
answer (a short segment away from all other paths), so the binary vertex count does not make the
problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`B₁`-CPG GRAPH RECOGNITION is NP-complete.** Source: Champseix, Galby, Munaro and Ries
(2021), Theorem 9; ISGCI, class `gc_1338`. -/
public theorem_wanted bOneCPGRecognition_npComplete :
    bOneCPGRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bOneCPGRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.BOneCPGRecognition
