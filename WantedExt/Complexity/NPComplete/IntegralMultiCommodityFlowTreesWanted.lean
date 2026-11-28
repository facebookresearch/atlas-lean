/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL K-MULTICOMMODITY FLOW ON TREES is NP-complete

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MAXIMUM INTEGRAL K-MULTICOMMODITY FLOW ON TREES;
N. Garg, V. V. Vazirani and M. Yannakakis, "Primal-dual approximation algorithms for integral
flow and multicut in trees", Algorithmica 18 (1997), 3-20, doi:10.1007/BF02523685.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntegralMultiCommodityFlowTreesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralMultiCommodityFlowTrees

/-!
# INTEGRAL K-MULTICOMMODITY FLOW ON TREES is NP-complete

INSTANCE: a tree `T = (V, E)`, a capacity function `c : E → ℕ`, `k` pairs of vertices
`(sᵢ, tᵢ)`, and a positive integer `K`.
QUESTION: is there a flow `fᵢ ∈ ℕ` for each pair `(sᵢ, tᵢ)` such that, for each `e ∈ E`,
`∑_{i=1}^k fᵢ qᵢ(e) ≤ c(e)`, where `qᵢ(e) = 1` if `e` belongs to the unique path from `sᵢ` to
`tᵢ` and `0` otherwise, and such that `∑_{i=1}^k fᵢ ≥ K`?

This is the decision version of MAXIMUM INTEGRAL K-MULTICOMMODITY FLOW ON TREES from the
Crescenzi-Kann compendium; Garg, Vazirani and Yannakakis prove the problem NP-hard
(MAX SNP-hard, even with edge capacities 1 and 2).

The tree is Mathlib's `SimpleGraph.IsTree` on the graph `Cslib.Complexity.Karp.edgeGraph` of the
edge list on `Fin n`. Each edge of the list carries its capacity, so the capacity function is
part of the edge list. The path from `sᵢ` to `tᵢ` is a Mathlib `SimpleGraph.Walk` with
`IsPath`; in a tree there is exactly one, so "some path from `sᵢ` to `tᵢ` contains `e`" is
"`e` belongs to the unique path". `WellFormed` requires `sᵢ ≠ tᵢ`: for `sᵢ = tᵢ` the path has
no edge and `fᵢ`, hence the measure of the optimization problem, would be unbounded (Könemann,
Parekh and Pritchard, Algorithmica 68 (2014), 776-804, likewise allow `sᵢ = tᵢ` only for vertex
capacities). The pairs form a list, so a pair may repeat.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INTEGRAL K-MULTICOMMODITY FLOW ON TREES is NP-complete.** Source: Crescenzi and Kann,
MAXIMUM INTEGRAL K-MULTICOMMODITY FLOW ON TREES; Garg, Vazirani and Yannakakis (1997). -/
public theorem_wanted integralMultiCommodityFlowTrees_npComplete :
    integralMultiCommodityFlowTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integralMultiCommodityFlowTreesDec

end MetaMathlibExt.Complexity.NPComplete.IntegralMultiCommodityFlowTrees
