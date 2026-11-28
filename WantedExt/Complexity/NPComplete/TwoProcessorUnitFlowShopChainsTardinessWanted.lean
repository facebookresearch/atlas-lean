/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR UNIT-TIME FLOW-SHOP TOTAL TARDINESS WITH CHAINS is NP-complete

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036
(`F2|pᵢⱼ = 1, chains|∑ Tⱼ` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Flow-shop problems without preemption" (`F2|pᵢⱼ = 1; chains|∑ Tᵢ`, minimal NP-hard,
credited to Brucker and Knust 1999).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitFlowShopChainsTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitFlowShopChainsTardiness

/-!
# TWO-PROCESSOR UNIT-TIME FLOW-SHOP TOTAL TARDINESS WITH CHAINS is NP-complete

INSTANCE: jobs `1, …, n` in a two-machine flow shop, job `j` consisting of an operation on
machine `M₁` followed by an operation on machine `M₂`, every operation of processing time
`pᵢⱼ = 1`; a precedence relation on the jobs consisting of disjoint chains (each job has at
most one immediate predecessor and at most one immediate successor); a due date `dⱼ ∈ ℤ₀⁺`
for each job; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a schedule (each machine processes at
most one operation at a time; the operation of job `j` on `M₂` starts only after its operation
on `M₁` is completed; if `j` precedes `k`, job `k` starts only after job `j` is completed) whose
total tardiness `∑ⱼ max(0, Cⱼ - dⱼ)` is at most `K`, `Cⱼ` being the completion time of job `j`
on `M₂`?

This is `F2|pᵢⱼ = 1; chains|∑ Tᵢ` in the three-field notation. Since every processing time is
`1`, processing times are not part of the instance. A schedule is given by the starting times
`s₁ j`, `s₂ j ∈ ℤ₀⁺` of the two operations of job `j`; non-overlap of two distinct jobs'
operations on one machine is `s + 1 ≤ s'` or `s' + 1 ≤ s` (the form of
`FlowShopSchedulingWanted`), job `k` starts at `s₁ k` and job `j` completes at
`Cⱼ = s₂ j + 1`, and `max(0, Cⱼ - dⱼ)` is the truncated subtraction `Cⱼ - dⱼ` of `ℕ`.

The chains are given by the list of their arcs `(j, k)`, `j` the immediate predecessor of `k`.
`WellFormed` requires every arc to name two jobs, no two arcs with the same tail or the same
head, and no cycle (the transitive closure `Relation.TransGen` of the arc relation is
irreflexive); the precedence relation is that transitive closure. The constraint is imposed on
the arcs; on the rest of the transitive closure it follows, since every job starts on `M₁`
before it completes on `M₂`. Jobs are `Fin n`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR UNIT-TIME FLOW-SHOP TOTAL TARDINESS WITH CHAINS is NP-complete.** Source:
Brucker and Knust (1999); Brucker and Knust's classification (`F2|pᵢⱼ = 1; chains|∑ Tᵢ`). -/
public theorem_wanted twoProcessorUnitFlowShopChainsTardiness_npComplete :
    twoProcessorUnitFlowShopChainsTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitFlowShopChainsTardinessDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitFlowShopChainsTardiness
