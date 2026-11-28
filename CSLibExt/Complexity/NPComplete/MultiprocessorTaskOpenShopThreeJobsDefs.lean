/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
# MULTIPROCESSOR-TASK OPEN SHOP OMPT|n=3|Cmax: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING, comment: remains
NP-complete if `m = 3`; T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time",
Journal of the ACM 23 (1976), 665-679, doi:10.1145/321978.321985; P. Brucker, *Scheduling
Algorithms*, 4th ed., Springer (2004), Chapter 11 (shop problems with multiprocessor tasks); P.
Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", entry `OMPT|n=3|C_max` (minimal NP-hard in the ordinary sense, citing Gonzalez and Sahni
1976).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopThreeJobs

open MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength eligible MPMWellFormed)

/-- `σ` is an MPT open-shop schedule: task `t` occupies every machine of `μ_t` during
`[σ t, σ t + p_t)`; two different tasks of positive length that share a machine, or that belong to
the same job, do not overlap. -/
def IsMPTOpenShopSchedule (i : MPMJobShopInstance) (σ : Operation i → ℕ) : Prop :=
  ∀ t t', t ≠ t' → ((∃ M ∈ eligible i t, M ∈ eligible i t') ∨ t.1 = t'.1) →
    0 < opLength i t → 0 < opLength i t' →
      σ t + opLength i t ≤ σ t' ∨ σ t' + opLength i t' ≤ σ t

/-- Well-formedness of an instance: a well-formed instance with its own machine count `m` (jobs with
at least one task, nonempty machine sets within `{1, …, m}`) and exactly three jobs. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed i.1 i ∧ i.2.1.length = 3

/-- Some MPT open-shop schedule completes every task by `K`. -/
def MultiprocessorTaskOpenShopThreeJobsFeasible (i : MPMJobShopInstance) : Prop :=
  ∃ σ : Operation i → ℕ, IsMPTOpenShopSchedule i σ ∧ ∀ t, σ t + opLength i t ≤ i.2.2

open Classical in
/-- MULTIPROCESSOR-TASK OPEN SHOP OMPT|n=3|Cmax as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopThreeJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopThreeJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopThreeJobs
