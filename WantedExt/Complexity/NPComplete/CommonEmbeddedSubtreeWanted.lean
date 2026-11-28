/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMON EMBEDDED SUBTREE is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MAXIMUM COMMON EMBEDDED SUB-TREE;
K. Zhang and T. Jiang, "Some MAX SNP-hard results concerning unordered labeled trees",
Information Processing Letters 49 (1994), 249-254, doi:10.1016/0020-0190(94)90062-0;
P. Kilpeläinen and H. Mannila, "Ordered and unordered tree inclusion", SIAM Journal on
Computing 24(2) (1995), 340-356, doi:10.1137/S0097539791218202 (unordered tree inclusion,
the case `K = |T₁|`, is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CommonEmbeddedSubtreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommonEmbeddedSubtree

/-!
# COMMON EMBEDDED SUBTREE is NP-complete

INSTANCE: rooted trees `T₁` and `T₂` with labels on the nodes, and a positive integer `K`.
QUESTION: is there a common embedded subtree of size at least `K`, i.e. a labeled tree `T'`
with `|T'| ≥ K` that can be embedded into both `T₁` and `T₂`? An embedding of `T'` into `T`
is an injective function from the nodes of `T'` to the nodes of `T` that preserves labels and
ancestorship. Since fathership need not be preserved, `T'` need not be an ordinary subtree.

Trees are unordered and given as in
`WantedExt.Complexity.NPComplete.UnorderedTreeEditDistanceWanted`: a list of
`(parent code, label)` pairs, code `0` for the root and `k + 1` for parent `k`. Preserving
ancestorship means that `x` is a proper ancestor of `y` in `T'` exactly when `f x` is a proper
ancestor of `f y` in `T`, as in the tree-inclusion embeddings of Kilpeläinen and Mannila.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COMMON EMBEDDED SUBTREE is NP-complete.** Source: Crescenzi and Kann, MAXIMUM COMMON EMBEDDED
SUB-TREE; Zhang and Jiang (1994); Kilpeläinen and Mannila (1995). -/
public theorem_wanted commonEmbeddedSubtree_npComplete :
    commonEmbeddedSubtreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L commonEmbeddedSubtreeDec

end MetaMathlibExt.Complexity.NPComplete.CommonEmbeddedSubtree
