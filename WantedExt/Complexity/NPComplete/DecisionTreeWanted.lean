/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DECISION TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS15] DECISION TREE;
L. Hyafil and R. L. Rivest, "Constructing optimal binary decision trees is
NP-complete", Information Processing Letters 5 (1976), 15-17,
doi:10.1016/0020-0190(76)90095-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DecisionTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DecisionTree

/-!
# DECISION TREE is NP-complete

INSTANCE: a finite set `X` of objects, a collection `T = {T₁, ..., T_m}` of binary tests
`Tᵢ : X → {0, 1}`, and a positive integer `K`. QUESTION: is there a decision tree for `X` using
the tests in `T` that has total external path length `K` or less?

A decision tree is a binary tree whose non-leaf vertices are labelled by tests from `T` and
whose leaves are labelled by objects from `X`; the edge from a non-leaf vertex to its left child
is labelled `0` and to its right child `1`. If `T_{i₁}, O₁, ..., T_{i_k}, O_k` are the vertex
and edge labels on the path from the root to a leaf labelled `x`, then `x` must be the unique
object with `T_{i_j}(x) = O_j` for all `j`. The total external path length is the sum, over
all leaves, of the number of edges from the root to the leaf.

Objects are `0, ..., n - 1`; test `t` sends object `x` to entry `x` of the `t`-th listed
Boolean vector.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DECISION TREE is NP-complete.** Source: Garey and Johnson (1979), [MS15]; Hyafil and
Rivest (1976). -/
public theorem_wanted decisionTree_npComplete :
    decisionTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L decisionTreeDec

end MetaMathlibExt.Complexity.NPComplete.DecisionTree
