/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL FLOW WITH MULTIPLIERS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND33] INTEGRAL FLOW WITH
MULTIPLIERS;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntegralFlowWithMultipliersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralFlowWithMultipliers

/-!
# INTEGRAL FLOW WITH MULTIPLIERS is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, a multiplier
`h(v) ∈ ℤ⁺` for each `v ∈ V - {s, t}`, a capacity `c(a) ∈ ℤ⁺` for each `a ∈ A`, and a
requirement `R ∈ ℤ⁺`. QUESTION: is there a flow function `f : A → ℤ₀⁺` such that
(1) `f(a) ≤ c(a)` for all `a ∈ A`, (2) for each `v ∈ V - {s, t}`,
`h(v) * ∑_{(u, v) ∈ A} f(u, v) = ∑_{(v, u) ∈ A} f(v, u)`, and (3) the net flow into `t` is at
least `R`?

Vertices are `0, ..., n - 1`. Arcs are listed as `(tail, head, capacity)` with distinct
`(tail, head)` pairs and distinct endpoints, and `f` assigns a natural number to each arc
position. Multipliers are listed for every vertex and read only at `v ∉ {s, t}`. Numbers are in
binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INTEGRAL FLOW WITH MULTIPLIERS is NP-complete.** Source: Garey and Johnson (1979),
[ND33]; Sahni (1974). -/
public theorem_wanted integralFlowWithMultipliers_npComplete :
    integralFlowWithMultipliersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integralFlowWithMultipliersDec

end MetaMathlibExt.Complexity.NPComplete.IntegralFlowWithMultipliers
