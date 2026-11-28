/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ELIMINATION DEGREE SEQUENCE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT47] ELIMINATION
DEGREE SEQUENCE (attributed there to Garey, Johnson, and Papadimitriou, 1977,
unpublished; transformation from EXACT COVER BY 3-SETS).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EliminationDegreeSequenceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EliminationDegreeSequence

/-!
# ELIMINATION DEGREE SEQUENCE is NP-complete

INSTANCE: a graph `G = (V, E)` and a sequence `⟨d₁, d₂, ..., d_|V|⟩` of non-negative integers
not exceeding `|V| - 1`. QUESTION: is there a one-to-one function `f : V → {1, 2, ..., |V|}`
such that, for `1 ≤ i ≤ |V|`, if `f(v) = i` then there are exactly `dᵢ` vertices `u` such that
`f(u) > i` and `{u, v} ∈ E`?

That is, when the vertices are removed in the order given by `f`, each vertex has exactly the
prescribed number of neighbours among the vertices not yet removed. (Garey and Johnson note that
the variant counting all neighbours of `v` is trivially solvable in polynomial time.)

Positions are 0-based here: `f : Fin |V| → Fin |V|` and position `i` reads `dᵢ₊₁`, the entry
of the list at index `i`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ELIMINATION DEGREE SEQUENCE is NP-complete.** Source: Garey and Johnson (1979), [GT47]
(Garey, Johnson, and Papadimitriou, 1977, unpublished). -/
public theorem_wanted eliminationDegreeSequence_npComplete :
    eliminationDegreeSequenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L eliminationDegreeSequenceDec

end MetaMathlibExt.Complexity.NPComplete.EliminationDegreeSequence
