/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EDGE-COST FLOW is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND32] MINIMUM EDGE-COST FLOW (p. 214;
credited there to S. Even and D. S. Johnson, 1977, unpublished; transformation from X3C).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumEdgeCostFlowDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumEdgeCostFlow

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted (IsFeasibleFlow)

/-!
# MINIMUM EDGE-COST FLOW is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, a capacity
`c(a) ∈ ℤ⁺` and a price `p(a) ∈ ℤ₀⁺` for each `a ∈ A`, a requirement `R ∈ ℤ⁺`, and a bound
`B ∈ ℤ⁺`.
QUESTION: is there a flow function `f : A → ℤ₀⁺` such that (1) `f(a) ≤ c(a)` for all `a ∈ A`,
(2) for each `v ∈ V - {s, t}`, `∑_{(u, v) ∈ A} f((u, v)) = ∑_{(v, u) ∈ A} f((v, u))`, i.e., flow is
"conserved" at `v`, (3) `∑_{(u, t) ∈ A} f((u, t)) - ∑_{(t, u) ∈ A} f((t, u)) ≥ R`, i.e., the net
flow into `t` is at least `R`, and (4) if `A' = {a ∈ A : f(a) ≠ 0}`, then `∑_{a ∈ A'} p(a) ≤ B`?

Vertices are `0, ..., n - 1`, and arcs are listed as `(tail, head, capacity, price)`. A flow is a
function `f : Fin n → Fin n → ℕ` on ordered pairs of vertices; conditions (1) and (2) are
MathlibExt's `IsFeasibleFlow` for the capacity `capacity i u v` (`0` off the arcs, so `f`
vanishes there), as in `DirectedTwoCommodityIntegralFlowWanted`. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM EDGE-COST FLOW is NP-complete.** Source: Garey and Johnson (1979), [ND32] (Even and
Johnson, 1977, unpublished). -/
public theorem_wanted minimumEdgeCostFlow_npComplete :
    minimumEdgeCostFlowDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumEdgeCostFlowDec

end MetaMathlibExt.Complexity.NPComplete.MinimumEdgeCostFlow
