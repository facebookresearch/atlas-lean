/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL FLOW WITH BUNDLES with unit capacities and two-arc bundles is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND36] INTEGRAL FLOW WITH
BUNDLES, p. 216, comment ("Remains NP-complete if all capacities are 1 and all bundles have two
arcs");
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021 (Problem N(iv), Theorem 2.2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntegralFlowBundlesUnitCapacitiesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralFlowBundlesUnitCapacities

open IntegralFlowBundles (IntegralFlowBundlesInstance IntegralFlowBundlesFeasible)

/-!
# INTEGRAL FLOW WITH BUNDLES with unit capacities and two-arc bundles is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, "bundles"
`I₁, I₂, ..., I_k ⊆ A` such that `⋃_{1 ≤ j ≤ k} I_j = A`, each consisting of two arcs, bundle
capacities `c₁ = c₂ = ... = c_k = 1`, and a requirement `R ∈ ℤ⁺`. QUESTION: is there a flow
function `f : A → ℤ₀⁺` such that (1) for `1 ≤ j ≤ k`, `∑_{a ∈ I_j} f(a) ≤ c_j`, (2) for each
`v ∈ V - {s, t}`, flow is conserved at `v`, and (3) the net flow into `t` is at least `R`?

Garey and Johnson record in the comment to [ND36] that the problem "remains NP-complete if all
capacities are 1 and all bundles have two arcs"; the reference they give for [ND36] is Sahni
(1974), a transformation from INDEPENDENT SET. Every arc lies in a bundle of capacity 1, so a
feasible flow is a 0-1 flow, a polynomial certificate, and the problem is in NP.

This is INTEGRAL FLOW WITH BUNDLES (`IntegralFlowBundlesWanted`) restricted to these instances.
The instance type, the parent well-formedness (`IntegralFlowBundles.WellFormed`: arcs on the
vertices `0, ..., n - 1` without self-loops or repeated arcs, `s` and `t` vertices, bundles of
arcs with positive capacities covering `A`, and `0 < R`) and the question
(`IntegralFlowBundles.IntegralFlowBundlesFeasible`) are the parent's, unchanged. As in the
parent, a bundle is the set of arcs in its list; the restriction adds to `WellFormed` that every
bundle `(I, c)` has capacity `c = 1` and exactly two distinct arcs (`I.toFinset.card = 2`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INTEGRAL FLOW WITH BUNDLES with unit capacities and two-arc bundles is NP-complete.**
Source: Garey and Johnson (1979), [ND36], comment; Sahni (1974). -/
public theorem_wanted integralFlowBundlesUnitCapacities_npComplete :
    integralFlowBundlesUnitCapacitiesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integralFlowBundlesUnitCapacitiesDec

end MetaMathlibExt.Complexity.NPComplete.IntegralFlowBundlesUnitCapacities
