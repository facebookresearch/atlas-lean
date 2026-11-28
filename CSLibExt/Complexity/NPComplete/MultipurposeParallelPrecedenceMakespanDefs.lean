/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE PARALLEL SCHEDULING WITH PRECEDENCE AND UNIT TIMES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING (the special case in which every machine set contains all machines);
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelPrecedenceMakespan

open MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule MPMWellFormed)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)

/-- An instance: an MPM job-shop instance (`m`, the jobs as lists of operations `(pᵢ, μᵢ)`, the
bound `K`) and the precedence arcs `(i, k)`. -/
abbrev MultipurposeParallelPrecedenceMakespanInstance := MPMJobShopInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: at least one machine (`m ∈ ℤ⁺`), a well-formed MPM job-shop
instance (machines `1, …, m`, nonempty machine sets) in which every job has exactly one
operation, of processing time `1`, and the arcs name jobs and form an acyclic digraph. -/
def WellFormed (i : MultipurposeParallelPrecedenceMakespanInstance) : Prop :=
  0 < i.1.1 ∧ MPMWellFormed i.1.1 i.1 ∧ (∀ job ∈ i.1.2.1, job.length = 1 ∧ ∀ o ∈ job, o.1 = 1) ∧
    PrecWellFormed i.1.2.1.length i.2

/-- Some MPM schedule of the jobs obeys the precedence arcs and completes every job by `K`. -/
def MultipurposeParallelPrecedenceMakespanFeasible
    (i : MultipurposeParallelPrecedenceMakespanInstance) : Prop :=
  ∃ a σ : Operation i.1 → ℕ, IsMPMJobShopSchedule i.1 a σ ∧
    (∀ t t' : Operation i.1, Prec i.2 t.1 t'.1 → σ t + opLength i.1 t ≤ σ t') ∧
    ∀ t, σ t + opLength i.1 t ≤ i.1.2.2

open Classical in
/-- `PMPM|prec; pᵢ = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelPrecedenceMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelPrecedenceMakespan
