/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG EDGE COLORING is NP-complete

Source:
M. Mahdian, "On the computational complexity of strong edge coloring", Discrete Applied
Mathematics 118 (2002), 239-248, doi:10.1016/S0166-218X(01)00237-2;
H. Hocquard, P. Ochem and P. Valicov, "Strong edge-colouring and induced matchings",
Information Processing Letters 113 (2013), 836-843, doi:10.1016/j.ipl.2013.07.026.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StrongEdgeColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongEdgeColoring

open MetaMathlibExt.Complexity.NPComplete.EdgeColoring (EdgeColoringInstance WellFormed)

/-!
# STRONG EDGE COLORING is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) and an integer `K` (`K = 0` is a
yes-instance only for an edgeless graph).
QUESTION: is there a strong edge coloring of `G` with at most `K` colors, that is, a coloring of
the edges in which two distinct edges get distinct colors whenever they share an endpoint or are
joined by an edge of `G` (equivalently, every color class is an induced matching)?

Mahdian proves that for every fixed `k ≥ 4` it is NP-complete to decide whether a bipartite
graph (of any prescribed girth) has a strong edge coloring with `k` colors; Hocquard, Ochem and
Valicov (abstract): "A strong edge-colouring of a graph `G` is a proper edge-colouring such that
every path of three edges uses three colours. … we prove the NP-completeness of strong 4-, 5-, and
6-edge-colouring … in some subclasses of subcubic triangle-free planar graphs." With `K` part of
the input the problem contains these fixed-`K` cases.

The instance type and its well-formedness are those of `EdgeColoringWanted`
(`EdgeColoring.EdgeColoringInstance`, `EdgeColoring.WellFormed`: a vertex count, a simple edge
list and `K`), and a coloring is given as there: a list with one color below `K` per listed edge.
`Near e f` says that the edges `e` and `f` share an endpoint or that some edge of `G` has one
endpoint on `e` and the other on `f`; a coloring is strong when edges at distinct positions that
are `Near` get distinct colors. Since the edge list has no repeated edge and no reversed copy,
distinct positions are distinct edges, and "every path of three edges uses three colours" for a
proper coloring is exactly this condition.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STRONG EDGE COLORING is NP-complete.** Source: Mahdian (2002); Hocquard, Ochem and
Valicov (2013). -/
public theorem_wanted strongEdgeColoring_npComplete :
    strongEdgeColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strongEdgeColoringDec

end MetaMathlibExt.Complexity.NPComplete.StrongEdgeColoring
