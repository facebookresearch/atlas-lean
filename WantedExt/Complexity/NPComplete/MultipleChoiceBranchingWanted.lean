/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE CHOICE BRANCHING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND11] MULTIPLE CHOICE
BRANCHING (credited there to Garey and Johnson, unpublished; transformation from
3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipleChoiceBranchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleChoiceBranching

/-!
# MULTIPLE CHOICE BRANCHING is NP-complete

INSTANCE: a directed graph `G = (V, A)`, a weight `w(a) ∈ Z⁺` for each arc `a ∈ A`, a partition
of `A` into disjoint sets `A₁, A₂, ..., Aₘ`, and a positive integer `K`. QUESTION: is there a
subset `A' ⊆ A` with `∑_{a ∈ A'} w(a) ≥ K` such that no two arcs in `A'` enter the same vertex,
`A'` contains no cycles, and `A'` contains at most one arc from each of the `Aᵢ`,
`1 ≤ i ≤ m`?

Vertices are `0, ..., n - 1`. Each arc carries the index of its partition class, so the classes
`Aᵢ` (arcs with equal class index) are disjoint and cover `A`. `A'` is a sublist of the arc
list. "No cycles" is the absence of a directed cycle: no vertex reaches itself by a nonempty
`Relation.TransGen` path along arcs of `A'`. Because no two arcs of `A'` enter the same vertex,
every cycle of the underlying undirected multigraph of `A'` is a directed cycle, so this is the
same as `A'` being a branching (a forest of out-trees). Weights use the canonical binary
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

/-- **MULTIPLE CHOICE BRANCHING is NP-complete.** Source: Garey and Johnson (1979), [ND11]. -/
public theorem_wanted multipleChoiceBranching_npComplete :
    multipleChoiceBranchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleChoiceBranchingDec

end MetaMathlibExt.Complexity.NPComplete.MultipleChoiceBranching
