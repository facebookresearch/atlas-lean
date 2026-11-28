/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LOCATING-DOMINATING SET is NP-complete

Source:
I. Charon, O. Hudry and A. Lobstein, "Minimizing the size of an identifying or
locating-dominating code in a graph is NP-hard", Theoretical Computer Science 290(3) (2003),
2109-2120, doi:10.1016/S0304-3975(02)00536-4;
M. R. Cappelle, G. C. M. Gomes and V. F. dos Santos, "Parameterized algorithms for
locating-dominating sets", arXiv:2011.14849 (2020), Section 1 (the problem as stated here, and
its NP-completeness, already for bipartite graphs, credited to Charon, Hudry and Lobstein).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LocatingDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LocatingDominatingSet

/-!
# LOCATING-DOMINATING SET is NP-complete

INSTANCE: a graph `G = (V, E)` and an integer `d`.
QUESTION: does `G` admit a locating-dominating set of size at most `d`, that is, a set
`S ⊆ V` that is dominating (every vertex is in `S` or adjacent to a vertex of `S`) and such
that `N_S(u) ≠ N_S(v)` for every pair of distinct vertices `u, v ∈ V \ S`, where
`N_S(u) = N(u) ∩ S`?

Domination is `SimpleGraph.IsDominating` from `MathlibExt.Combinatorics.SimpleGraph.Domination`,
and `N(u)` is Mathlib's `SimpleGraph.neighborSet`. The bound `d` uses the canonical binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LOCATING-DOMINATING SET is NP-complete.** Source: Charon, Hudry and Lobstein (2003). -/
public theorem_wanted locatingDominatingSet_npComplete :
    locatingDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L locatingDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.LocatingDominatingSet
