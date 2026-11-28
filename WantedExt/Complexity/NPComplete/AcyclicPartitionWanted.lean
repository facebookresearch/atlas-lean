/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACYCLIC PARTITION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND15] ACYCLIC
PARTITION (credited there to Garey and Johnson, unpublished; transformation from
X3C).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AcyclicPartitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AcyclicPartition

/-!
# ACYCLIC PARTITION is NP-complete

INSTANCE: a directed graph `G = (V, A)`, a weight `w(v) ∈ Z⁺` for each `v ∈ V`, a cost
`c(a) ∈ Z⁺` for each `a ∈ A`, and positive integers `B` and `K`. QUESTION: is there a partition
of `V` into disjoint sets `V₁, ..., Vₘ` such that the directed graph `G' = (V', A')`, where
`V' = {V₁, ..., Vₘ}` and `(Vᵢ, Vⱼ) ∈ A'` if and only if `(vᵢ, vⱼ) ∈ A` for some `vᵢ ∈ Vᵢ` and some
`vⱼ ∈ Vⱼ` (`i ≠ j`), is acyclic, such that the sum of the weights of the vertices in each `Vᵢ`
does not exceed `B`, and such that the sum of the costs of all those arcs having their
endpoints in different sets does not exceed `K`?

Vertices are `0, ..., n - 1`. A partition is given by a block label `p v` for every vertex;
the blocks are the nonempty fibres of `p`. `quotientArc` is the arc relation of `G'` on block
labels (arcs inside one block give no arc of `G'`), and "acyclic" is the absence of a directed
cycle: no block reaches itself by a nonempty `Relation.TransGen` path. Weights and costs use the
canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ACYCLIC PARTITION is NP-complete.** Source: Garey and Johnson (1979), [ND15]. -/
public theorem_wanted acyclicPartition_npComplete :
    acyclicPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L acyclicPartitionDec

end MetaMathlibExt.Complexity.NPComplete.AcyclicPartition
