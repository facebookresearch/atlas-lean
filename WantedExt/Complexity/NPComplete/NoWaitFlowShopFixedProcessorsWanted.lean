/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT FLOW-SHOP SCHEDULING with a fixed number `m ≥ 4` of processors is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (comment: "NP-complete in the strong sense for any fixed `m ≥ 4`", credited to
Papadimitriou and Kanellakis);
C. H. Papadimitriou and P. C. Kanellakis, "Flowshop scheduling with limited temporary
storage", Journal of the ACM 27 (1980), 533-549, doi:10.1145/322203.322213.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.NoWaitFlowShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopFixedProcessors

/-!
# NO-WAIT FLOW-SHOP SCHEDULING with a fixed number `m ≥ 4` of processors is NP-complete

For a fixed constant `m ≥ 4`: INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of `m`
tasks `t₁[j], …, tₘ[j]` (with `tᵢ[j]` to be executed by processor `i`), a length `l(t) ∈ ℤ₀⁺`
for each such task `t`, and an overall deadline `D ∈ ℤ⁺`. QUESTION: is there a flow-shop
schedule for `J` that meets the overall deadline and has the property that, for each `j ∈ J`
and `1 ≤ i < m`, `σᵢ₊₁(j) = σᵢ(j) + l(tᵢ[j])`?

This is the restriction of NO-WAIT FLOW-SHOP SCHEDULING ([SS16],
`NoWaitFlowShopSchedulingWanted`) to instances with exactly `m` processors, for a constant `m`
that is not part of the instance. The instance type, `NoWaitFlowShopScheduling.WellFormed` and
`NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingFeasible` are the parent's, unchanged;
`WellFormed m` adds that the instance's number of processors is `m`. Garey and Johnson state
the result for every fixed `m ≥ 4`; Papadimitriou and Kanellakis prove it for four processors.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the fixed number `m` of processors: the parent's
(`0 < m`, every job has `m` tasks, `0 < D`) and the instance has exactly `m` processors. -/
def WellFormed (m : ℕ) (i : NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) :
    Prop :=
  NoWaitFlowShopScheduling.WellFormed i ∧ i.1 = m

open Classical in
/-- NO-WAIT FLOW-SHOP SCHEDULING with the number of processors fixed to `m`, as a decision
problem over bitstrings. -/
noncomputable def noWaitFlowShopFixedProcessorsDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) x with
  | some i => decide (WellFormed m i ∧
      NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingFeasible i)
  | none => false

/-- **NO-WAIT FLOW-SHOP SCHEDULING is NP-complete for every fixed number `m ≥ 4` of
processors.** Source: Garey and Johnson (1979), [SS16], comment; Papadimitriou and Kanellakis
(1980). -/
public theorem_wanted noWaitFlowShopFixedProcessors_npComplete (m : ℕ) (hm : 4 ≤ m) :
    noWaitFlowShopFixedProcessorsDec m ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (noWaitFlowShopFixedProcessorsDec m)

end MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopFixedProcessors
