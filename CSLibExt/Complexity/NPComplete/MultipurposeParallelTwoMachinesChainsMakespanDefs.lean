/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS: definitions

Source:
J. Du, J. Y.-T. Leung and G. H. Young, "Scheduling chain-structured tasks to minimize makespan
and mean flow time", Information and Computation 92 (1991), 219-236,
doi:10.1016/0890-5401(91)90009-Q;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines) and Table 5.3 (`P2|chains|C_max`, NP-hard in the
strong sense, Du et al.).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLatenessDefs
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsMakespan

open MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule MPMWellFormed)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)
open MultiprocessorTaskFlowShopTreeLateness (ImmediatePredecessor)

/-- An instance: an MPM job-shop instance (`m`, the jobs as lists of operations `(pᵢ, μᵢ)`, the
bound `K`) and the precedence arcs `(i, k)`. -/
abbrev MultipurposeParallelTwoMachinesChainsMakespanInstance := MPMJobShopInstance × List (ℕ × ℕ)

/-- The precedence relation of the arcs is a set of chains: every job has at most one immediate
successor and at most one immediate predecessor. -/
def IsChains (i : MultipurposeParallelTwoMachinesChainsMakespanInstance) : Prop :=
  (∀ j a b : Fin i.1.2.1.length, ImmediatePredecessor i.2 j a → ImmediatePredecessor i.2 j b →
    a = b) ∧
    ∀ j a b : Fin i.1.2.1.length, ImmediatePredecessor i.2 a j → ImmediatePredecessor i.2 b j →
      a = b

/-- Well-formedness of an instance: a well-formed MPM job-shop instance with `m = 2` machines
(nonempty machine sets in `{1, 2}`) in which every job has exactly one operation, of positive
processing time, and the arcs name jobs, form an acyclic digraph, and describe a set of chains. -/
def WellFormed (i : MultipurposeParallelTwoMachinesChainsMakespanInstance) : Prop :=
  MPMWellFormed 2 i.1 ∧ (∀ job ∈ i.1.2.1, job.length = 1 ∧ ∀ o ∈ job, 0 < o.1) ∧
    PrecWellFormed i.1.2.1.length i.2 ∧ IsChains i

/-- Some MPM schedule of the jobs obeys the precedence arcs and completes every job by `K`. -/
def MultipurposeParallelTwoMachinesChainsMakespanFeasible
    (i : MultipurposeParallelTwoMachinesChainsMakespanInstance) : Prop :=
  ∃ a σ : Operation i.1 → ℕ, IsMPMJobShopSchedule i.1 a σ ∧
    (∀ t t' : Operation i.1, Prec i.2 t.1 t'.1 → σ t + opLength i.1 t ≤ σ t') ∧
    ∀ t, σ t + opLength i.1 t ≤ i.1.2.2

open Classical in
/-- `PMPM2|chains|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesChainsMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesChainsMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelTwoMachinesChainsMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsMakespan
