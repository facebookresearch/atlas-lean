/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH CONSTRAINED NETWORK FLOW with unit capacities is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND34] PATH CONSTRAINED NETWORK FLOW
(p. 215), comment "Remains NP-complete even if all c(a) = 1" (credited there to H. J. Prömel,
1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PathConstrainedNetworkFlowWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlowUnit

open MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlow
  (PathConstrainedNetworkFlowInstance)

/-!
# PATH CONSTRAINED NETWORK FLOW with unit capacities is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, the capacity `c(a) = 1`
for each `a ∈ A`, a collection `P` of directed paths in `G`, and a requirement `R ∈ ℤ⁺`.
QUESTION: is there a function `g : P → ℤ₀⁺` whose induced flow `f(a) = ∑_{p ∈ P(a)} g(p)` is
within the capacities, conserved at every `v ∈ V - {s, t}`, and has net flow into `t` at least
`R`?

This is the restriction of PATH CONSTRAINED NETWORK FLOW ([ND34],
`PathConstrainedNetworkFlowWanted`) to instances in which every capacity is `1`. The instance
type, `PathConstrainedNetworkFlow.WellFormed` and
`PathConstrainedNetworkFlow.PathConstrainedNetworkFlowFeasible` are the parent's, unchanged;
`WellFormed` adds that every arc has capacity `1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (a directed graph on `0, ..., n - 1` with
positive capacities, distinct vertices `s` and `t`, every member of `P` a directed path in `G`,
`0 < R`) and every capacity is `1`. -/
def WellFormed (i : PathConstrainedNetworkFlowInstance) : Prop :=
  PathConstrainedNetworkFlow.WellFormed i ∧ ∀ a ∈ i.2.1, a.2.2 = 1

open Classical in
/-- PATH CONSTRAINED NETWORK FLOW with unit capacities as a decision problem over bitstrings. -/
noncomputable def pathConstrainedNetworkFlowUnitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathConstrainedNetworkFlowInstance) x with
  | some i =>
    decide (WellFormed i ∧ PathConstrainedNetworkFlow.PathConstrainedNetworkFlowFeasible i)
  | none => false

/-- **PATH CONSTRAINED NETWORK FLOW is NP-complete with unit capacities.** Source: Garey and
Johnson (1979), [ND34], comment (Prömel, 1978). -/
public theorem_wanted pathConstrainedNetworkFlowUnit_npComplete :
    pathConstrainedNetworkFlowUnitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathConstrainedNetworkFlowUnitDec

end MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlowUnit
