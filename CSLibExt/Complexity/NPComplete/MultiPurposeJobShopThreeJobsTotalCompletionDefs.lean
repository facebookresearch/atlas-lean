/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM3|n=3|ΣC_i: definitions

Source:
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N;
recorded in P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `JMPM3|n=3|ΣC_i`, minimal NP-hard in the ordinary sense, Sotskov and Shakhlevich
(1995));
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM job shop
model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsTotalCompletion

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule
  MPMWellFormed)

/-- Well-formedness of an instance: a well-formed MPM job shop instance with `m = 3` machines
(every job nonempty, every operation with a nonempty set of eligible machines in `{1, 2, 3}`) and
exactly three jobs. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed 3 i ∧ i.2.1.length = 3

/-- Some MPM job shop schedule has `Σ_j C_j ≤ K`, where `C j` is the completion time of the last
operation of job `j`. -/
def MultiPurposeJobShopThreeJobsTotalCompletionFeasible (i : MPMJobShopInstance) :
    Prop :=
  ∃ a σ : Operation i → ℕ, IsMPMJobShopSchedule i a σ ∧
    ∃ C : Fin i.2.1.length → ℕ,
      (∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
        C j = σ ⟨j, k⟩ + opLength i ⟨j, k⟩) ∧
      ∑ j : Fin i.2.1.length, C j ≤ i.2.2

open Classical in
/-- MULTIPURPOSE-MACHINE JOB SHOP `JMPM3|n=3|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def multiPurposeJobShopThreeJobsTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMJobShopInstance) x with
  | some i =>
      decide (WellFormed i ∧ MultiPurposeJobShopThreeJobsTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsTotalCompletion
