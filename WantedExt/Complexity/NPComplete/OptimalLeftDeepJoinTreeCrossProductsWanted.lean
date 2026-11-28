/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL LEFT-DEEP JOIN TREE WITH CROSS PRODUCTS is NP-complete

Source:
S. Cluet and G. Moerkotte, "On the complexity of generating optimal left-deep processing trees
with cross products", in *Database Theory - ICDT '95*, Lecture Notes in Computer Science 893,
Springer (1995), 54-67, doi:10.1007/3-540-58907-4_6 (NP-hardness for the cost function `C_out`,
by a reduction from 3-DIMENSIONAL MATCHING, already for star queries);
G. Moerkotte, *Building Query Compilers*, Section 3.1 (cardinalities, selectivities and `C_out`)
and Section 3.1.6 (the complexity table, "general/tree/star, left-deep, cross products: yes,
ASI: NP-hard", credited to Cluet and Moerkotte).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OptimalLeftDeepJoinTreeCrossProductsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalLeftDeepJoinTreeCrossProducts

/-!
# OPTIMAL LEFT-DEEP JOIN TREE WITH CROSS PRODUCTS is NP-complete

INSTANCE: relations `R₁, …, Rₙ`, `n ≥ 1`, with cardinalities `|Rᵢ| ∈ ℤ⁺`, a selectivity
`f_{i,j} = f_{j,i} ∈ (0, 1]` for each pair of relations joined by a predicate (`f_{i,j} = 1` for
the other pairs, whose join is a cross product, and `f_{i,i} = 1`), and an integer `K`.
QUESTION: is there a left-deep processing tree, cross products allowed, whose cost `C_out` is at
most `K`?

The cardinality model and the cost function are those of Moerkotte (Section 3.1), the model of
Cluet and Moerkotte: the output cardinality of a join tree `T = T₁ ⋈ T₂` is
`|T| = (∏_{Rᵢ ∈ T₁, Rⱼ ∈ T₂} f_{i,j}) |T₁| |T₂|`, so the relations `s₁, …, s_k` joined in any
order have `|s₁, …, s_k| = ∏_{a ≤ k} |s_a| · ∏_{a < b ≤ k} f_{s_a, s_b}`, and
`C_out(T) = 0` for a single relation and `C_out(T₁ ⋈ T₂) = |T₁ ⋈ T₂| + C_out(T₁) + C_out(T₂)`:
the sum of the output cardinalities of all joins in `T`. A left-deep tree joins the relations
one at a time in a sequence `s₁, …, sₙ`; when cross products are allowed every sequence is one,
so the trees are the permutations `π` (`s_{a+1} = R_{π a}`) and
`C_out = ∑_{k = 2}^{n} |s₁, …, s_k|`, which includes the final join (the same for every order,
so leaving it out only shifts `K`).

Cluet and Moerkotte prove the problem NP-hard for `C_out` by a reduction from 3-DIMENSIONAL
MATCHING, even for star queries (Moerkotte, Section 3.1.6). Membership in NP: the order is a
certificate, and `C_out` is a sum of `n - 1` products of `O(n²)` input numbers, computed in
polynomial time.

The relations are `Fin n`, one per listed cardinality. A selectivity is listed once, as
`(i, j, p, q)` with `i < j` and `f_{i,j} = p / q`, `0 < p ≤ q`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **OPTIMAL LEFT-DEEP JOIN TREE WITH CROSS PRODUCTS is NP-complete.** Source: Cluet and
Moerkotte (1995); Moerkotte, *Building Query Compilers*, Sections 3.1 and 3.1.6. -/
public theorem_wanted optimalLeftDeepJoinTreeCrossProducts_npComplete :
    optimalLeftDeepJoinTreeCrossProductsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L optimalLeftDeepJoinTreeCrossProductsDec

end MetaMathlibExt.Complexity.NPComplete.OptimalLeftDeepJoinTreeCrossProducts
