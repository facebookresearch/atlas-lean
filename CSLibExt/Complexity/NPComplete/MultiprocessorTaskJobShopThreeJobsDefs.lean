/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|Cmax: definitions

Source:
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (shop problems with
multiprocessor tasks: the MPT job-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", entry `JMPT3|n=3|C_max` (minimal NP-hard in the ordinary sense, citing Sotskov and
Shakhlevich 1995);
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N
(`J3|n=3|C_max` is NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobs

open MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength eligible MPMWellFormed)

/-- `σ` is an MPT job shop schedule: task `t` occupies every machine of `μ_t` during
`[σ t, σ t + p_t)`; two different tasks of positive length whose machine sets share a machine do
not overlap; and every task of a job starts no earlier than the previous task of the job
completes. -/
def IsMPTJobShopSchedule (i : MPMJobShopInstance) (σ : Operation i → ℕ) : Prop :=
  (∀ t t', t ≠ t' → (∃ M ∈ eligible i t, M ∈ eligible i t') → 0 < opLength i t →
      0 < opLength i t' → σ t + opLength i t ≤ σ t' ∨ σ t' + opLength i t' ≤ σ t) ∧
    ∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + opLength i ⟨j, k⟩ ≤ σ ⟨j, k'⟩

/-- Well-formedness of an instance: a well-formed instance with `m = 3` machines (jobs with at
least one task, nonempty machine sets within `{1, 2, 3}`) and exactly three jobs. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed 3 i ∧ i.2.1.length = 3

/-- Some MPT job shop schedule has makespan at most `K`: the last task of every job, which
completes after the job's other tasks, completes by `K`. -/
def MultiprocessorTaskJobShopThreeJobsFeasible (i : MPMJobShopInstance) : Prop :=
  ∃ σ : Operation i → ℕ, IsMPTJobShopSchedule i σ ∧
    ∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
      σ ⟨j, k⟩ + opLength i ⟨j, k⟩ ≤ i.2.2

open Classical in
/-- MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|Cmax as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskJobShopThreeJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskJobShopThreeJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobs
