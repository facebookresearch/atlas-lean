/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL FLOW WITH HOMOLOGOUS ARCS with unit capacities is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND35] INTEGRAL FLOW WITH
HOMOLOGOUS ARCS, p. 215, comment ("Remains NP-complete if c(a) = 1 for all a ∈ A (by modifying
the construction in [Even, Itai, and Shamir, 1976])");
S. Even, A. Itai and A. Shamir, "On the complexity of timetable and multicommodity flow
problems", SIAM Journal on Computing 5 (1976), 691-703, doi:10.1137/0205048.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntegralFlowHomologousArcsUnitCapacitiesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralFlowHomologousArcsUnitCapacities

open IntegralFlowHomologousArcs
  (IntegralFlowHomologousArcsInstance IntegralFlowHomologousArcsFeasible)

/-!
# INTEGRAL FLOW WITH HOMOLOGOUS ARCS with unit capacities is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, capacity `c(a) = 1`
for each `a ∈ A`, a requirement `R ∈ ℤ⁺`, and a set `H ⊆ A × A` of "homologous" pairs of arcs.
QUESTION: is there a flow function `f : A → ℤ₀⁺` such that (1) `f(a) ≤ c(a)` for all `a ∈ A`,
(2) for each `v ∈ V - {s, t}`, flow is conserved at `v`, (3) for all pairs `⟨a, a'⟩ ∈ H`,
`f(a) = f(a')`, and (4) the net flow into `t` is at least `R`?

Garey and Johnson record in the comment to [ND35] that the problem "remains NP-complete if
`c(a) = 1` for all `a ∈ A`", by modifying the construction of Even, Itai and Shamir (their
reduction from 3SAT to two-commodity integral flow). With unit capacities a feasible flow is a
0-1 flow, a polynomial certificate, so the problem is in NP.

This is INTEGRAL FLOW WITH HOMOLOGOUS ARCS (`IntegralFlowHomologousArcsWanted`) restricted to
unit capacities. The instance type, the parent well-formedness
(`IntegralFlowHomologousArcs.WellFormed`: arcs on the vertices `0, ..., n - 1` without
self-loops or repeated arcs, positive capacities, `s` and `t` vertices, `0 < R`, and
`H ⊆ A × A`) and the question (`IntegralFlowHomologousArcs.IntegralFlowHomologousArcsFeasible`)
are the parent's, unchanged; the restriction adds to `WellFormed` that every arc record
`(u, v, c)` has capacity `c = 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INTEGRAL FLOW WITH HOMOLOGOUS ARCS with unit capacities is NP-complete.** Source: Garey
and Johnson (1979), [ND35], comment; Even, Itai and Shamir (1976). -/
public theorem_wanted integralFlowHomologousArcsUnitCapacities_npComplete :
    integralFlowHomologousArcsUnitCapacitiesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integralFlowHomologousArcsUnitCapacitiesDec

end MetaMathlibExt.Complexity.NPComplete.IntegralFlowHomologousArcsUnitCapacities
