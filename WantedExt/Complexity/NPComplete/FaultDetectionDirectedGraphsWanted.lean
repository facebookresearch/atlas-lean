/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FAULT DETECTION IN DIRECTED GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [MS18] FAULT DETECTION IN DIRECTED GRAPHS,
p. 283, crediting T. Ibaraki, T. Kameda and S. Toida, "NP-complete diagnosis problems on systems
graphs", unpublished manuscript (1977) (transformation from X3C).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FaultDetectionDirectedGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FaultDetectionDirectedGraphs

/-!
# FAULT DETECTION IN DIRECTED GRAPHS is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)`, with `I ⊆ V` the vertices of in-degree `0` and
`O ⊆ V` the vertices of out-degree `0`, and a positive integer `K`.
QUESTION: is there a "test set" of size `K` or less that can detect every "single fault" in `G`,
i.e. a subset `T ⊆ I × O` with `|T| ≤ K` such that for every `v ∈ V` some pair `(u₁, u₂) ∈ T`
has `v` on a directed path from `u₁` to `u₂` in `G`?

`v` lies on a directed path from `u₁` to `u₂` exactly when `u₁` reaches `v` and `v` reaches
`u₂` (`Relation.ReflTransGen` of the arc relation): in an acyclic digraph every directed walk is
a directed path, so the two walks concatenate to a path through `v`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FAULT DETECTION IN DIRECTED GRAPHS is NP-complete.** Source: Garey and Johnson (1979),
[MS18]; Ibaraki, Kameda and Toida (1977). -/
public theorem_wanted faultDetectionDirectedGraphs_npComplete :
    faultDetectionDirectedGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L faultDetectionDirectedGraphsDec

end MetaMathlibExt.Complexity.NPComplete.FaultDetectionDirectedGraphs
