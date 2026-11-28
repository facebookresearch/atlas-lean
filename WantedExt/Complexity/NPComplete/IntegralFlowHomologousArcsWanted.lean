/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL FLOW WITH HOMOLOGOUS ARCS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND35] INTEGRAL FLOW WITH
HOMOLOGOUS ARCS;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021 (Problem N(iii), Theorem 2.2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntegralFlowHomologousArcsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralFlowHomologousArcs

/-!
# INTEGRAL FLOW WITH HOMOLOGOUS ARCS is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, a capacity
`c(a) ∈ ℤ⁺` for each `a ∈ A`, a requirement `R ∈ ℤ⁺`, and a set `H ⊆ A × A` of "homologous"
pairs of arcs. QUESTION: is there a flow function `f : A → ℤ₀⁺` such that (1) `f(a) ≤ c(a)` for
all `a ∈ A`, (2) for each `v ∈ V - {s, t}`, flow is conserved at `v`, (3) for all pairs
`⟨a, a'⟩ ∈ H`, `f(a) = f(a')`, and (4) the net flow into `t` is at least `R`?

The vertices are `0, ..., n - 1`. Each arc is a record `(u, v, c)`: the arc from `u` to `v` with
capacity `c`; there are no self-loops and no repeated arcs. A homologous pair is a pair
`((u, v), (u', v'))` of arcs, each given by its endpoints. A flow is a function
`f : Fin n → Fin n → ℕ` (integral and nonnegative) on ordered pairs. Conditions (1) and (2) are
`IsFeasibleFlow` from `MathlibExt.Combinatorics.Graph.MaxFlowMinCut` for the arc capacities
`capacity` (`c(a)` on an arc `a`, `0` on every other ordered pair), so the flow also vanishes
off the arcs, i.e. it is a function on `A`. Conditions (3) and (4) are stated directly. As in
the source, `s` and `t` need not be distinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/-- **INTEGRAL FLOW WITH HOMOLOGOUS ARCS is NP-complete.** Source: Garey and Johnson (1979),
[ND35]; Sahni (1974). -/
public theorem_wanted integralFlowHomologousArcs_npComplete :
    integralFlowHomologousArcsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integralFlowHomologousArcsDec

end MetaMathlibExt.Complexity.NPComplete.IntegralFlowHomologousArcs
