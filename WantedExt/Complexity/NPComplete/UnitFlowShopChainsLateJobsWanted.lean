/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP F2|p_ij=1;chains|ΣU_i is NP-complete

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_nop` (flow-shop problems without preemption), Universität Osnabrück (last update 2006).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import WantedExt.Complexity.NPComplete.TwoProcessorUnitFlowShopChainsTardinessWanted
public import WantedExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopChainsLateJobs

open UnitFlowShopTransportationDelays (IsUnitFlowShopSchedule)
open TwoProcessorUnitFlowShopChainsTardiness
  (TwoProcessorUnitFlowShopChainsTardinessInstance Job dueDate Arc)

/-!
# FLOW SHOP F2|p_ij=1;chains|ΣU_i is NP-complete

INSTANCE: `n` jobs, each consisting of two unit-time operations, the first on machine `M₁` and
the second on machine `M₂` (the second cannot start before the first is completed); a
precedence relation on the jobs consisting of disjoint chains (each job has at most one
immediate predecessor and at most one immediate successor), where `i` preceding `j` means that
no operation of `j` starts before every operation of `i` is completed; for each job `j` a due
date `d_j ∈ ℤ₀⁺`; a bound `K`. Each machine processes at most one operation at a time.
QUESTION: is there a schedule in which the number of late jobs, the jobs `j` whose completion
time `C_j` (that of their second operation) exceeds `d_j`, is at most `K`?

In the three-field notation this is `F2|p_ij=1; chains|∑ U_i`. Brucker and Knust's
classification lists it as minimal strongly NP-hard, citing Brucker and Knust (1999), whose
complexity results for single-machine problems with constant positive time-lags "also lead to
new results for flow-shop problems with unit processing times and job precedences".

The instance, jobs, due dates, chain arcs and well-formedness are those of
`TwoProcessorUnitFlowShopChainsTardinessWanted` (`F2|p_ij=1; chains|∑ T_i`), reused unchanged:
the chains are given by the list of immediate-predecessor pairs `(j, k)`, and `WellFormed`
requires that every pair names two jobs, that no job has two immediate successors or two
immediate predecessors, and that the pairs have no cycle. Enforcing the listed immediate
precedences enforces the whole chain order, since it is their transitive closure.

A schedule is the repository's unit-time two-machine flow-shop schedule `IsUnitFlowShopSchedule`
with zero delays: each machine runs a one-processor schedule of its unit operations and a job's
second operation starts after its first is completed. Start times are natural numbers: with
integer data, shifting every operation of a feasible schedule as early as its machine order
allows gives an integral schedule with no later completion times, so this does not change the
answer. The jobs are `Fin n`, one per listed due date. Binary encoding of all numbers (the problem
is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some unit-time two-machine flow-shop schedule obeys the chains (job `b` starts on `M₁` only
after its immediate predecessor `a` completes on `M₂`) and has at most `K` late jobs: jobs `j`
with `d_j < C_j`, where `C_j = σ 1 j + 1`. -/
def UnitFlowShopChainsLateJobsFeasible (i : TwoProcessorUnitFlowShopChainsTardinessInstance) :
    Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitFlowShopSchedule (fun _ => 0) σ ∧
    (∀ a b, Arc i a b → σ 1 a + 1 ≤ σ 0 b) ∧
    (Finset.univ.filter fun j => dueDate i j < σ 1 j + 1).card ≤ i.2.2

open Classical in
/-- FLOW SHOP `F2|p_ij=1;chains|∑ U_i` as a decision problem over bitstrings. -/
noncomputable def unitFlowShopChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitFlowShopChainsTardinessInstance) x with
  | some i =>
    decide (TwoProcessorUnitFlowShopChainsTardiness.WellFormed i ∧
      UnitFlowShopChainsLateJobsFeasible i)
  | none => false

/-- **FLOW SHOP `F2|p_ij=1;chains|∑ U_i` is NP-complete.** Source: Brucker and Knust (1999);
Brucker and Knust, scheduling classification, class `f_nop`. -/
public theorem_wanted unitFlowShopChainsLateJobs_npComplete :
    unitFlowShopChainsLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitFlowShopChainsLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopChainsLateJobs
