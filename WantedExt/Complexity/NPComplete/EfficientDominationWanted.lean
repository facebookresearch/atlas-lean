/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EFFICIENT DOMINATION (PERFECT CODE) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EFFICIENT DOMINATION; D.
G. Corneil and Y. Perl, "Clustering and domination in perfect graphs" (1984) and the perfect-
code literature.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EfficientDominationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EfficientDomination

/-!
# EFFICIENT DOMINATION (PERFECT CODE) is NP-complete

An undirected graph. The question is whether the graph has an efficient dominating set (a
perfect code): a set `S` such that every vertex has exactly one closed neighbor in `S`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EFFICIENT DOMINATION (PERFECT CODE) is NP-complete.** The decision problem EFFICIENT
DOMINATION belongs to NP, and every decision problem in NP reduces to it by a polynomial-time
many-one reduction.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), EFFICIENT DOMINATION; D. G. Corneil and Y.
Perl, "Clustering and domination in perfect graphs" (1984) and the perfect-code
literature. -/
public theorem_wanted efficientDomination_npComplete :
    efficientDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L efficientDominationDec

end MetaMathlibExt.Complexity.NPComplete.EfficientDomination
