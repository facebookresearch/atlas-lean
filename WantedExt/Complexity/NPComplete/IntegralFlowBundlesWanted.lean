/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL FLOW WITH BUNDLES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND36] INTEGRAL FLOW WITH
BUNDLES;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021 (Problem N(iv), Theorem 2.2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntegralFlowBundlesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralFlowBundles

/-!
# INTEGRAL FLOW WITH BUNDLES is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, "bundles"
`I₁, I₂, ..., I_k ⊆ A` such that `⋃_{1 ≤ j ≤ k} I_j = A`, bundle capacities
`c₁, c₂, ..., c_k ∈ ℤ⁺`, and a requirement `R ∈ ℤ⁺`. QUESTION: is there a flow function
`f : A → ℤ₀⁺` such that (1) for `1 ≤ j ≤ k`, `∑_{a ∈ I_j} f(a) ≤ c_j`, (2) for each
`v ∈ V - {s, t}`, flow is conserved at `v`, and (3) the net flow into `t` is at least `R`?

The vertices are `0, ..., n - 1` and the arcs are a list of ordered pairs without repetitions or
self-loops. A bundle is a record `(I, c)`: a list `I` of arcs and its capacity `c`; a bundle is
the set of arcs in its list, so repeated entries in `I` do not count twice. Bundles may overlap.
A flow is a function `f : Fin n → Fin n → ℕ` (integral and nonnegative) on ordered pairs that
vanishes off the arcs, i.e. a function on `A`. Arcs have no individual capacities: every arc
lies in some bundle, which bounds its flow. As in the source, `s` and `t` need not be distinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INTEGRAL FLOW WITH BUNDLES is NP-complete.** Source: Garey and Johnson (1979), [ND36];
Sahni (1974). -/
public theorem_wanted integralFlowBundles_npComplete :
    integralFlowBundlesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integralFlowBundlesDec

end MetaMathlibExt.Complexity.NPComplete.IntegralFlowBundles
