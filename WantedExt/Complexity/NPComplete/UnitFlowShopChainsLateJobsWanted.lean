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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relation
public import WantedExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopChainsLateJobs

open UnitFlowShopTransportationDelays (IsUnitFlowShopSchedule)

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

The chains are given by the list of immediate-predecessor pairs `(a, b)` ("`a` immediately
precedes `b`"); `WellFormed` requires that every pair names two jobs, that no job has two
immediate successors or two immediate predecessors, and that the pairs have no directed cycle
(`IsChains`). Enforcing the listed immediate precedences enforces the whole chain order, since
it is their transitive closure. A schedule is the repository's unit-time two-machine flow-shop
schedule `IsUnitFlowShopSchedule` with zero delays: each machine runs a one-processor schedule of
its unit operations and a job's second operation starts after its first is completed. Start
times are natural numbers: with integer data, shifting every operation of a feasible schedule as
early as its machine order allows gives an integral schedule with no later completion times, so
this does not change the answer. The jobs are `Fin n`, one per listed due date. Binary encoding
of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The pairs `arcs` (`(a, b)`: job `a` immediately precedes job `b`) form disjoint chains on
the jobs `0, …, n - 1`: every pair names two jobs, no job has two immediate successors or two
immediate predecessors, and there is no directed cycle (so no job precedes itself). -/
def IsChains (n : ℕ) (arcs : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ arcs, e.1 < n ∧ e.2 < n) ∧
    (∀ e ∈ arcs, ∀ e' ∈ arcs, e.1 = e'.1 → e = e') ∧
    (∀ e ∈ arcs, ∀ e' ∈ arcs, e.2 = e'.2 → e = e') ∧
    ∀ v, ¬ Relation.TransGen (fun a b => (a, b) ∈ arcs) v v

/-- An instance: the due dates `d_j`, one per job; the immediate-predecessor pairs of the chains;
and the bound `K`. -/
abbrev UnitFlowShopChainsLateJobsInstance := List ℕ × List (ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed due dates. -/
abbrev Job (i : UnitFlowShopChainsLateJobsInstance) : Type := Fin i.1.length

/-- The due date `d_j` of job `j`. -/
def dueDate (i : UnitFlowShopChainsLateJobsInstance) (j : Job i) : ℕ :=
  i.1.get j

/-- Job `a` immediately precedes job `b`: the pair `(a, b)` is listed. -/
def Prec (i : UnitFlowShopChainsLateJobsInstance) (a b : Job i) : Prop :=
  ((a : ℕ), (b : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the listed pairs form disjoint chains on the jobs. -/
def WellFormed (i : UnitFlowShopChainsLateJobsInstance) : Prop :=
  IsChains i.1.length i.2.1

/-- Some unit-time two-machine flow-shop schedule obeys the chains (job `b` starts on `M₁` only
after its immediate predecessor `a` completes on `M₂`) and has at most `K` late jobs: jobs `j`
with `d_j < C_j`, where `C_j = σ 1 j + 1`. -/
def UnitFlowShopChainsLateJobsFeasible (i : UnitFlowShopChainsLateJobsInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitFlowShopSchedule (fun _ => 0) σ ∧
    (∀ a b, Prec i a b → σ 1 a + 1 ≤ σ 0 b) ∧
    (Finset.univ.filter fun j => dueDate i j < σ 1 j + 1).card ≤ i.2.2

open Classical in
/-- FLOW SHOP `F2|p_ij=1;chains|∑ U_i` as a decision problem over bitstrings. -/
noncomputable def unitFlowShopChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ UnitFlowShopChainsLateJobsFeasible i)
  | none => false

/-- **FLOW SHOP `F2|p_ij=1;chains|∑ U_i` is NP-complete.** Source: Brucker and Knust (1999);
Brucker and Knust, scheduling classification, class `f_nop`. -/
public theorem_wanted unitFlowShopChainsLateJobs_npComplete :
    unitFlowShopChainsLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitFlowShopChainsLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopChainsLateJobs
