/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on 2-subdivision graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT, comment ("Remains
NP-complete if `w(e) = 1` for all `e ∈ E` (the SIMPLE MAX CUT problem)");
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1 (SIMPLE MAX
CUT);
ISGCI, *Information System on Graph Classes and their Inclusions*, class "2-subdivision"
(gc_472, https://www.graphclasses.org/classes/gc_472.html), problem Maximum cut: NP-complete,
reference [1648] (a note communicated by P. Irzhavski, section "Maximum cut").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SimpleMaxCutTwoSubdivisionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutTwoSubdivision

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)
open MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementTwoSubdivisionPlanar
  (IsTwoSubdivision)

/-!
# SIMPLE MAX CUT on 2-subdivision graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is a 2-subdivision, and a positive integer `K`. A
2-subdivision of a graph `H` results from inserting two new vertices in every edge, that is,
from replacing each edge `uv` of `H` by a path `u x y v` with new vertices `x, y`; `G` is a
2-subdivision if it is the 2-subdivision of some graph (ISGCI's class 2-subdivision, gc_472).
QUESTION: is there a partition of `V` into two sets with at least `K` edges between them?

This is SIMPLE MAX CUT (MAX CUT with all edge weights one, [ND16]) restricted to 2-subdivision
graphs. The instance, the simple-edge-list conditions and the question are those of MAXIMUM CUT
(`MaxCutDefs`, whose question counts edges), reused as in `SimpleMaxCutCubicWanted`; the class
is the predicate `IsTwoSubdivision` of `MinimumCutLinearArrangementTwoSubdivisionPlanarWanted`
(the graph is isomorphic to the 2-subdivision of a simple graph given by a simple edge list),
applied to `Cslib.Complexity.Karp.edgeGraph`, and `0 < K` ([ND16]'s positive integer `K`).
Isolated vertices do not change the answer, so the binary vertex count does not make the problem
succinct.

Hardness, as in ISGCI's note [1648]: if a graph `H` has `m` edges and a maximum cut of size
`k`, its 2-subdivision `H'` has a maximum cut of size exactly `2m + k`. A cut of `H` extends to
`H'` cutting all three edges of the path `u x y v` replacing a cut edge `uv` and two of the
three otherwise; conversely, from a cut of `H'` of size `l`, cutting `uv` exactly when an odd
number of `ux, xy, yv` are cut gives a cut of `H` of size at least `l - 2m`. So
`(H, k) ↦ (H', 2m + k)` reduces SIMPLE MAX CUT to this problem. Membership in NP: the partition
is a certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SIMPLE MAX CUT on 2-subdivision graphs is NP-complete.** Source: ISGCI, class gc_472,
reference [1648]; Garey, Johnson and Stockmeyer (1976); Garey and Johnson (1979), [ND16]. -/
public theorem_wanted simpleMaxCutTwoSubdivision_npComplete :
    simpleMaxCutTwoSubdivisionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutTwoSubdivisionDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutTwoSubdivision
