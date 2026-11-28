/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE UNIFORM PARALLEL MACHINE SCHEDULING `QMPM|chains;p_i=1|C_max`: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multipurpose machine problems" (`QMPM|chains;p_i=1|C_max`,
minimal NP-hard in the strong sense, citing W. Kubiak, "Exact and approximate algorithms for
scheduling unit time tasks with tree-like precedence constraints", Abstracts EURO IX - TIMS
XXVIII, Paris (1988), 195; that abstract was not available to us);
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 2.7 (`P2|chain, fix_j, p_j = 1|C_max`, the case of
two machines of speed `1` and one-machine sets);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.Order.Field.Rat
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelPrecedenceMakespanDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeUniformMachinesUnitChainsMakespan

open MultiPurposeJobShopThreeJobs (Operation opLength eligible)
open UnitFlowShopPrecedenceMakespan (Prec)
open MultipurposeParallelPrecedenceMakespan (MultipurposeParallelPrecedenceMakespanInstance)

/-- An instance: a `PMPM|prec;p_i=1|C_max` instance (the number `m` of machines, the jobs as lists
of operations `(p_i, μ_i)`, the bound `K`, the precedence arcs) and the speeds, the `k`-th pair
`(a, b)` being the speed `s_k = a / b` of machine `M_k`. -/
abbrev MultipurposeUniformMachinesUnitChainsMakespanInstance :=
  MultipurposeParallelPrecedenceMakespanInstance × List (ℕ × ℕ)

/-- The speed `s_k = a / b` of machine `M_k`, `k ∈ {1, …, m}`, from the `k`-th listed pair
`(a, b)`. -/
def speed (i : MultipurposeUniformMachinesUnitChainsMakespanInstance) (k : ℕ) : ℚ :=
  ((i.2.getD (k - 1) (1, 1)).1 : ℚ) / (i.2.getD (k - 1) (1, 1)).2

/-- The completion time `C_t = σ(t) + p_t / s_{a(t)}` of job `t` started at time `σ(t)` on
machine `a(t)`. -/
def completion (i : MultipurposeUniformMachinesUnitChainsMakespanInstance)
    (a : Operation i.1.1 → ℕ) (σ : Operation i.1.1 → ℚ) (t : Operation i.1.1) : ℚ :=
  σ t + (opLength i.1.1 t : ℚ) / speed i (a t)

/-- Well-formedness of an instance: a well-formed `PMPM|prec;p_i=1|C_max` instance (`m ≥ 1`,
every job one operation of processing time `1` with a nonempty machine set in `{1, …, m}`, arcs
that name jobs and form an acyclic digraph) whose arcs form a set of chains, with exactly `m`
speeds, each `a / b` with `0 < a` and `0 < b`. -/
def WellFormed (i : MultipurposeUniformMachinesUnitChainsMakespanInstance) : Prop :=
  MultipurposeParallelPrecedenceMakespan.WellFormed i.1 ∧
    MultipurposeParallelTwoMachinesUnitChainsMakespan.IsChains i.1 ∧
    i.2.length = i.1.1.1 ∧ ∀ s ∈ i.2, 0 < s.1 ∧ 0 < s.2

/-- Some schedule, a machine `a(t) ∈ μ_t` and a start time `σ(t) ≥ 0` for each job `t`, has
makespan at most `K`: two different jobs on the same machine do not overlap, `C_t ≤ σ(t')` for
every arc `(t, t')`, and every job completes by `K`. -/
def MultipurposeUniformMachinesUnitChainsMakespanFeasible
    (i : MultipurposeUniformMachinesUnitChainsMakespanInstance) : Prop :=
  ∃ (a : Operation i.1.1 → ℕ) (σ : Operation i.1.1 → ℚ),
    (∀ t, a t ∈ eligible i.1.1 t) ∧ (∀ t, 0 ≤ σ t) ∧
    (∀ t t', t ≠ t' → a t = a t' →
      completion i a σ t ≤ σ t' ∨ completion i a σ t' ≤ σ t) ∧
    (∀ t t' : Operation i.1.1, Prec i.1.2 t.1 t'.1 → completion i a σ t ≤ σ t') ∧
    ∀ t, completion i a σ t ≤ i.1.1.2.2

open Classical in
/-- `QMPM|chains;p_i=1|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeUniformMachinesUnitChainsMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeUniformMachinesUnitChainsMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeUniformMachinesUnitChainsMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeUniformMachinesUnitChainsMakespan
