/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EDGE-COST FLOW with capacities 2 and prices 0/1 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND32] MINIMUM EDGE-COST FLOW (p. 214),
comment "Remains NP-complete if c(a) = 2 and p(a) ∈ {0,1} for all a ∈ A" (credited there to
S. Even and D. S. Johnson, 1977, unpublished).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumEdgeCostFlowTwoZeroOneDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumEdgeCostFlowTwoZeroOne

open MetaMathlibExt.Complexity.NPComplete.MinimumEdgeCostFlow (MinimumEdgeCostFlowInstance)

/-!
# MINIMUM EDGE-COST FLOW with capacities 2 and prices 0/1 is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, the capacity `c(a) = 2`
and a price `p(a) ∈ {0, 1}` for each `a ∈ A`, a requirement `R ∈ ℤ⁺`, and a bound `B ∈ ℤ⁺`.
QUESTION: is there a flow function `f : A → ℤ₀⁺` within the capacities, conserved at every
`v ∈ V - {s, t}`, with net flow into `t` at least `R`, such that the arcs carrying nonzero flow
have total price at most `B`?

This is the restriction of MINIMUM EDGE-COST FLOW ([ND32], `MinimumEdgeCostFlowWanted`) to
instances in which every capacity is `2` and every price is `0` or `1`. The instance type,
`MinimumEdgeCostFlow.WellFormed` and `MinimumEdgeCostFlow.MinimumEdgeCostFlowFeasible` are the
parent's, unchanged; `WellFormed` adds the two restrictions on the arc records. Garey and Johnson
record that the problem is solvable in polynomial time if every capacity is `1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM EDGE-COST FLOW is NP-complete with capacities `2` and prices `0`/`1`.** Source:
Garey and Johnson (1979), [ND32], comment (Even and Johnson, 1977, unpublished). -/
public theorem_wanted minimumEdgeCostFlowTwoZeroOne_npComplete :
    minimumEdgeCostFlowTwoZeroOneDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumEdgeCostFlowTwoZeroOneDec

end MetaMathlibExt.Complexity.NPComplete.MinimumEdgeCostFlowTwoZeroOne
