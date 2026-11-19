/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEDICATED-PROCESSOR SCHEDULING `P2|chains;p_i=1;fix_i|ΣC_i` is NP-complete

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994),
259-272, doi:10.1016/0166-218X(94)90012-4, Theorem 3.6;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multiprocessor task problems with dedicated processors"
(`P2|chains;p_i=1;fix_i|ΣC_i`, minimal NP-hard in the strong sense).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsMakespan
  (TwoProcessorUnitDedicatedChainsInstance WellFormed IsSchedule)

/-!
# DEDICATED-PROCESSOR SCHEDULING `P2|chains;p_i=1;fix_i|ΣC_i` is NP-complete

INSTANCE: `m = 2` processors, each processing at most one task at a time; tasks `1, …, n`, each
with unit processing time `p_i = 1` and a prespecified set `fix_i ⊆ {1, 2}` of processors, all
of which it requires simultaneously during its processing (so two tasks whose sets intersect
cannot overlap in time); a precedence relation on the tasks consisting of chains (every task has
at most one immediate predecessor and at most one immediate successor): if `i` precedes `j`,
then `j` cannot start before `i` is completed; and a positive integer `K`. QUESTION: is there a
feasible schedule whose total completion time `Σ_i C_i` is at most `K`, where `C_i` is the
completion time of task `i`?

The instance, its well-formedness (`m = 2`, nonempty processor sets without repetitions of
processors below `2`, chain arcs with the conditions of `F3UnitChainsLateJobs.ChainsWellFormed`,
and `K > 0`) and the schedules (`IsSchedule`: start times `s i ∈ ℕ` such that two different tasks
with a common processor run in disjoint unit time intervals and every chain arc `(i, j)` has
`s i + 1 ≤ s j`) are those of `TwoProcessorUnitDedicatedChainsMakespanWanted`
(`P2|chains;p_i=1;fix_i|C_max`), reused unchanged; the last number of the instance is here the
bound on `Σ_i C_i`, with `C_i = s i + 1`. Binary encoding of all numbers (the problem is
NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some schedule has total completion time `Σ_j (s j + 1)` at most `K`. -/
def TwoProcessorUnitDedicatedChainsTotalCompletionFeasible
    (i : TwoProcessorUnitDedicatedChainsInstance) : Prop :=
  ∃ s, IsSchedule i s ∧ (∑ j, (s j + 1)) ≤ i.1.2.2

open Classical in
/-- `P2|chains;p_i=1;fix_i|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def twoProcessorUnitDedicatedChainsTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitDedicatedChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitDedicatedChainsTotalCompletionFeasible i)
  | none => false

/-- **DEDICATED-PROCESSOR SCHEDULING `P2|chains;p_i=1;fix_i|ΣC_i` is NP-complete.** Source:
Hoogeveen, van de Velde and Veltman (1994), Theorem 3.6. -/
public theorem_wanted twoProcessorUnitDedicatedChainsTotalCompletion_npComplete :
    twoProcessorUnitDedicatedChainsTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitDedicatedChainsTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsTotalCompletion
