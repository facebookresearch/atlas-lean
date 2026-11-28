/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH GRUNDY NUMBERING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT56] GRAPH GRUNDY NUMBERING;
J. van Leeuwen, "Having a Grundy-numbering is NP-complete", Report No. 207, Computer Science
Department, Pennsylvania State University (1976);
A. S. Fraenkel, "Planar kernel and Grundy with d ≤ 3, d_out ≤ 2, d_in ≤ 2 are NP-complete",
Discrete Applied Mathematics 3 (1981), 257-262, doi:10.1016/0166-218X(81)90003-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphGrundyNumberingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphGrundyNumbering

/-!
# GRAPH GRUNDY NUMBERING is NP-complete

Given a directed graph `G = (V, A)`, is there a function `f : V → {0, 1, 2, …}` such that, for
each `v ∈ V`, `f(v)` is the least non-negative integer not contained in the set
`{f(u) : (v, u) ∈ A}`?

The digraph has vertices `Fin n` and is given by its arc list; it is finite, with no loops
and no multiple arcs (`WellFormed`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH GRUNDY NUMBERING is NP-complete.** Source: Garey and Johnson (1979), [GT56];
van Leeuwen (1976); Fraenkel (1981). -/
public theorem_wanted graphGrundyNumbering_npComplete :
    graphGrundyNumberingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphGrundyNumberingDec

end MetaMathlibExt.Complexity.NPComplete.GraphGrundyNumbering
