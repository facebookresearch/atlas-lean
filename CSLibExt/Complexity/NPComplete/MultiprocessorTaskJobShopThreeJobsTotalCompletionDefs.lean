/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|ΣC_i: definitions

Source:
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (shop problems with
multiprocessor tasks: the MPT job-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", entry `JMPT3|n=3|ΣC_i` (minimal NP-hard in the ordinary sense, citing Sotskov and
Shakhlevich 1995);
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N
(`J3|n=3|ΣC_i` is NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobsTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength)
open MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobs
  (WellFormed IsMPTJobShopSchedule)

/-- Some MPT job shop schedule has total completion time at most `K`: values `C j`, each at
least the completion time of the last task of job `j`, sum to at most `K`. -/
def MultiprocessorTaskJobShopThreeJobsTotalCompletionFeasible (i : MPMJobShopInstance) : Prop :=
  ∃ (σ : Operation i → ℕ) (C : Fin i.2.1.length → ℕ), IsMPTJobShopSchedule i σ ∧
    (∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
      σ ⟨j, k⟩ + opLength i ⟨j, k⟩ ≤ C j) ∧ ∑ j, C j ≤ i.2.2

open Classical in
/-- MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|ΣC_i as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskJobShopThreeJobsTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskJobShopThreeJobsTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobsTotalCompletion
