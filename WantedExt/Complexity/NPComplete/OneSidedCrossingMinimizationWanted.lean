/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ONE-SIDED CROSSING MINIMIZATION is NP-complete

Source:
P. Eades and N. C. Wormald, "Edge crossings in drawings of bipartite graphs", Algorithmica 11(4)
(1994), 379-403, doi:10.1007/BF01187020;
X. Muñoz, W. Unger and I. Vrt'o, "One sided crossing minimization is NP-hard for sparse graphs",
Graph Drawing (GD 2001), LNCS 2265 (2002), 115-123, doi:10.1007/3-540-45848-4_10.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OneSidedCrossingMinimizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OneSidedCrossingMinimization

/-!
# ONE-SIDED CROSSING MINIMIZATION is NP-complete

INSTANCE: a bipartite graph `G = (U, W, E)`, a fixed linear order of `U`, and a nonnegative
integer `K`. QUESTION: is there a linear order of `W` such that the two-layer straight-line
drawing of `G` (the vertices of `U` on one line in the fixed order, those of `W` on a parallel
line in the chosen order, edges as straight segments) has at most `K` crossings?

The two vertex classes are listed explicitly, as duplicate-free lists of natural-number names:
the list of `U` is in the fixed order, and a linear order of `W` is a list that is a permutation of
the list of `W`, the position of a vertex being its index (`List.idxOf`). Edges are pairs
`(u, w)` with `u` in `U` and `w` in `W`, listed without repetition (a simple bipartite graph).
In a two-layer straight-line drawing, the edges `(u₁, w₁)` and `(u₂, w₂)` cross exactly when
their endpoints appear in opposite orders on the two lines: `u₁` before `u₂` and `w₂` before
`w₁`, or vice versa; edges sharing an endpoint do not cross. The number of crossings is therefore
the number of ordered pairs of edges with `u₁` before `u₂` and `w₂` before `w₁`, each crossing
pair being counted once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ONE-SIDED CROSSING MINIMIZATION is NP-complete.** Source: Eades and Wormald (1994); Muñoz,
Unger and Vrt'o (2002). -/
public theorem_wanted oneSidedCrossingMinimization_npComplete :
    oneSidedCrossingMinimizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L oneSidedCrossingMinimizationDec

end MetaMathlibExt.Complexity.NPComplete.OneSidedCrossingMinimization
