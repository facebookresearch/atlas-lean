/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O2|p_ij=1;chains|Σw_iC_i is NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `o_nop` (open-shop problems without preemption), Universität Osnabrück (last update 2006).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.UnitFlowShopChainsWeightedCompletionWanted
public import WantedExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopChainsWeightedCompletion

open UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)
open UnitFlowShopChainsWeightedCompletion (weight)
open TwoProcessorUnitFlowShopChainsTardiness
  (TwoProcessorUnitFlowShopChainsTardinessInstance Job WellFormed)

/-!
# OPEN SHOP O2|p_ij=1;chains|Σw_iC_i is NP-complete

INSTANCE: `n` jobs, each consisting of two unit-time operations, one on machine `M₁` and one on
machine `M₂`, which may be processed in either order but not at the same time; a precedence
relation on the jobs consisting of disjoint chains (each job has at most one immediate
predecessor and at most one immediate successor), where `i` preceding `j` means that no
operation of `j` starts before every operation of `i` is completed; for each job `j` a weight
`w_j ∈ ℤ₀⁺`; a bound `K`. Each machine processes at most one operation at a time. QUESTION: is
there a schedule whose total weighted completion time `∑_j w_j C_j` is at most `K`, where `C_j`
is the completion time of job `j`'s last operation?

In the three-field notation this is `O2|p_ij=1; chains|∑ w_i C_i`. Brucker and Knust's
classification lists it as minimal strongly NP-hard, citing Timkovsky (2003), whose paper
relates unit-time open shops with chains to preemptive scheduling on identical parallel
machines; the full text was not available to this formalization.

The instance, the jobs, the weights and the well-formedness are those of the flow shop
`F2|p_ij=1; chains|∑ w_i C_i` (`UnitFlowShopChainsWeightedCompletionWanted`, which reuses the
instance of `TwoProcessorUnitFlowShopChainsTardinessWanted`): the `j`-th listed number is `w_j`,
the listed pairs `(j, k)` are the chain arcs (`j` the immediate predecessor of `k`), and
`WellFormed` asks that every arc name two jobs, that no two distinct arcs share their tail or
their head, and that the arcs have no cycle. Only the schedule differs: in an open shop the
operations of a job have no prescribed order. A schedule is the unit-time open-shop schedule
`IsUnitOpenShopSchedule` of `UnitOpenShopOutTreeMaxLatenessWanted` on two machines with the
chain arcs as precedence arcs: the operations on one machine, and the two operations of one job,
start at different times, and every operation of a job starts after every operation of its
immediate predecessor is completed (which gives the same for every predecessor along the
chain). The completion time is `C_j = max(σ₁(j), σ₂(j)) + 1`. Start times are natural numbers:
with unit operations and integer data, fixing the order of the operations on each machine and
within each job, and starting every operation as early as these orders and the chains allow,
gives an integral schedule whose completion times are no later, so this does not change the
answer. Binary encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some unit-time two-machine open-shop schedule obeys the chains and has total weighted
completion time `∑_j w_j C_j` at most `K`, where `C_j = max (σ 0 j) (σ 1 j) + 1`. -/
def UnitOpenShopChainsWeightedCompletionFeasible
    (i : TwoProcessorUnitFlowShopChainsTardinessInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitOpenShopSchedule 2 i.1.length i.2.1 σ ∧
    ∑ j, weight i j * (max (σ 0 j) (σ 1 j) + 1) ≤ i.2.2

open Classical in
/-- OPEN SHOP `O2|p_ij=1;chains|∑ w_i C_i` as a decision problem over bitstrings. -/
noncomputable def unitOpenShopChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitFlowShopChainsTardinessInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopChainsWeightedCompletionFeasible i)
  | none => false

/-- **OPEN SHOP `O2|p_ij=1;chains|∑ w_i C_i` is NP-complete.** Source: Timkovsky (2003); Brucker
and Knust, scheduling classification, class `o_nop`. -/
public theorem_wanted unitOpenShopChainsWeightedCompletion_npComplete :
    unitOpenShopChainsWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitOpenShopChainsWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopChainsWeightedCompletion
