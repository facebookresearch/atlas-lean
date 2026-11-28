/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on graphs of maximum degree 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT, comment ("Remains
NP-complete if `w(e) = 1` for all `e ∈ E` (the SIMPLE MAX CUT problem) [...], and if, in
addition, no vertex has degree exceeding 3");
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proc. 10th Annual ACM
Symposium on Theory of Computing (1978), 253-264, doi:10.1145/800133.804355.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SimpleMaxCutDegreeThreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutDegreeThree

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT on graphs of maximum degree 3 is NP-complete

INSTANCE: a graph `G = (V, E)` in which no vertex has degree exceeding 3, and a positive
integer `K`. QUESTION: is there a partition of `V` into disjoint sets `V₁` and `V₂` such that
at least `K` edges of `E` have one endpoint in `V₁` and one endpoint in `V₂`?

This is the restriction of MAXIMUM CUT with unit weights
(`CSLibExt.Complexity.NPComplete.MaxCutDefs`, whose question already counts edges) to
graphs of maximum degree 3. The instance, the simple-edge-list conditions, and the question
are those of that module, reused here; the degree bound uses Mathlib's `SimpleGraph.degree`
on `Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SIMPLE MAX CUT on graphs of maximum degree 3 is NP-complete.** Source: Garey and Johnson
(1979), [ND16], comment; Yannakakis (1978). -/
public theorem_wanted simpleMaxCutDegreeThree_npComplete :
    simpleMaxCutDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutDegreeThree
