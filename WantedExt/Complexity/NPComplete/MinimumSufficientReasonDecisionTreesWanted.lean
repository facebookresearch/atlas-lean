/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SUFFICIENT REASON for decision trees is NP-complete

Source:
P. Barceló, M. Monet, J. Pérez and B. Subercaseaux, "Model interpretability through the lens
of computational complexity", Advances in Neural Information Processing Systems 33
(NeurIPS 2020), Proposition 6 (1) and Lemma 18; arXiv:2010.12265.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumSufficientReasonDecisionTreesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSufficientReasonDecisionTrees

open StatMech.OSSS

/-!
# MINIMUM SUFFICIENT REASON for decision trees is NP-complete

INSTANCE: a decision tree `T` over the Boolean features `1, ..., n`, an instance
`x ∈ {0, 1}ⁿ`, and `k ∈ ℕ`. QUESTION: is there a sufficient reason `y` for `x` with respect to
`T` with `‖y‖ ≤ k`?

Following Barceló, Monet, Pérez and Subercaseaux (2020), Section 3: a partial instance is a
vector `y ∈ {0, 1, ⊥}ⁿ`, and `x` is a completion of `y` when `xᵢ = yᵢ` wherever `yᵢ ≠ ⊥`. A
sufficient reason for `x` is a partial instance `y` of which `x` is a completion and such that
`T(x') = T(x)` for every completion `x'` of `y`; `‖y‖` is the number of components of `y` other
than `⊥`. A partial instance of which `x` is a completion is determined by the set `S` of its
defined components (its values there are those of `x`), so the question asks for a set `S` of
at most `k` features such that every `x'` agreeing with `x` on `S` has `T(x') = T(x)`. A
decision tree is a free binary decision diagram (no two nodes on a root-to-leaf path carry the
same feature) whose underlying graph is a tree; the source proves NP-completeness for free
binary decision diagrams and hardness already for decision trees.

Representation: features are `Fin n`, with `n` the length of the listed instance `x`; the tree
is `StatMech.OSSS.DecisionTree (Fin n)`, whose node `node e t f` continues in `t` when feature
`e` is `1` and in `f` when it is `0`. The instance lists the tree in preorder: the token
`(true, e)` is a node querying feature `e`, followed by its `1`-subtree and then its
`0`-subtree; `(false, 1)` and `(false, 0)` are leaves labelled true and false. Each token is
one node, so the token list has the size of the tree.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM SUFFICIENT REASON for decision trees is NP-complete.** Source: Barceló, Monet,
Pérez and Subercaseaux (2020), Proposition 6 (1) and Lemma 18. -/
public theorem_wanted minimumSufficientReasonDecisionTrees_npComplete :
    minimumSufficientReasonDecisionTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumSufficientReasonDecisionTreesDec

end MetaMathlibExt.Complexity.NPComplete.MinimumSufficientReasonDecisionTrees
