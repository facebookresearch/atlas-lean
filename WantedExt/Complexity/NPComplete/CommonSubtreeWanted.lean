/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMON SUBTREE is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM COMMON SUBTREE;
T. Akutsu and M. M. Halldórsson, "On the approximation of largest common subtrees and largest
common point sets", Theoretical Computer Science 233 (2000), 33-50,
doi:10.1016/S0304-3975(97)00278-8 (conference version: Proc. ISAAC 1994, LNCS 834, 405-413,
doi:10.1007/3-540-58325-4_205).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CommonSubtreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommonSubtree

/-!
# COMMON SUBTREE is NP-complete

INSTANCE: a collection `T₁, …, T_n` of trees and a positive integer `K`. QUESTION: is there a
tree `T'` with at least `K` vertices that is isomorphic to a subtree (an induced connected
subgraph) of each `Tᵢ`?

This is the decision version of MAXIMUM COMMON SUBTREE in the compendium of Crescenzi and Kann,
whose measure is the number of vertices of `T'`. The trees are unlabeled and unrooted.

Each tree is a vertex count `n` and an edge list on `Fin n` (`Cslib.Complexity.Karp.edgeGraph`),
a simple edge list (no duplicates, loops or reversed copies) whose graph is a tree
(`SimpleGraph.IsTree`: connected and acyclic). `T'` is a tree on `Fin m` with `K ≤ m`, and
"`T'` is isomorphic to a subtree of `Tᵢ`" is a graph embedding `T' ↪g Tᵢ`
(`SimpleGraph.Embedding`: an injective map that preserves and reflects adjacency). Its image is a
vertex set whose induced subgraph of `Tᵢ` is isomorphic to `T'`, hence connected; conversely an
induced connected subgraph of a tree is a tree. The collection is nonempty (`n ≥ 1`); with no
trees every `K` would be a yes-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COMMON SUBTREE is NP-complete.** Source: Crescenzi and Kann, MAXIMUM COMMON SUBTREE;
Akutsu and Halldórsson (2000). -/
public theorem_wanted commonSubtree_npComplete :
    commonSubtreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L commonSubtreeDec

end MetaMathlibExt.Complexity.NPComplete.CommonSubtree
