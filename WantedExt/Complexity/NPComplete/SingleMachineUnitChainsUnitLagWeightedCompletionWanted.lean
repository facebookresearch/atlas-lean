/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE SCHEDULING WITH UNIT TIME LAGS `1|chains(1);p_i=1|Σw_iC_i` is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Single machine
problems with non-negative time-lags" (University of Osnabrück, last updated 2003), minimal
NP-hard problem (strong sense) `1|chains(1);p_i=1|Σw_iC_i`, citing
V. S. Tanaev, Y. N. Sotskov and V. A. Strusevich, *Scheduling Theory. Multi-Stage Systems*,
Mathematics and its Applications 285, Kluwer Academic Publishers, Dordrecht (1994),
doi:10.1007/978-94-011-1192-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted
public import WantedExt.Complexity.NPComplete.SingleMachineChainsTimeLagMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleMachineUnitChainsUnitLagWeightedCompletion

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)
open SingleMachineChainsTimeLagMakespan (SingleMachineChainsTimeLagMakespanInstance)

/-!
# SINGLE-MACHINE SCHEDULING WITH UNIT TIME LAGS `1|chains(1);p_i=1|Σw_iC_i` is NP-complete

INSTANCE: one machine that processes at most one job at a time; jobs `1, …, n`, each with unit
processing time `p_i = 1` and a weight `w_i ∈ ℤ₀⁺`; a precedence relation consisting of
disjoint chains (each job has at most one immediate predecessor and at most one immediate
successor), every precedence pair `i → j` carrying the unit finish-start time lag, i.e.
`S_j ≥ C_i + 1`; and an integer bound `K`.
QUESTION: is there a feasible schedule with total weighted completion time `Σ_i w_i C_i ≤ K`,
where `S_i` is the start and `C_i = S_i + 1` the completion time of job `i`?

In Brucker and Knust's notation, `chains(1)` is a chain precedence relation in which every
precedence pair carries the unit time lag (`(l)` is one lag `l` shared by all pairs, see
`SingleMachineChainsTimeLagMakespanWanted`). Their table lists `1|chains(1);p_i=1|Σw_iC_i` as
minimal NP-hard in the strong sense, citing Tanaev, Sotskov and Strusevich (1994); the book
itself was not available to this formalization.

The instance data and well-formedness are those of `SingleMachineChainsTimeLagMakespanWanted`
(`1|chains(l)|C_max`), with the job list carrying weights instead of processing times: the
instance type `SingleMachineChainsTimeLagMakespanInstance` (the `j`-th listed number is now the
weight `w_j` of job `j`), the chains as lists of job indices (consecutive jobs in a chain are an
immediate predecessor and successor; no job in two chains or twice in a chain), the time lag
`l`, required here to be `1`, and the bound `K`; that module's `WellFormed` is reused. Jobs are
not preempted; a schedule gives every job `j` a start time `S j`, two unit jobs never overlap
(Garey and Johnson's one-processor schedule [SS1] with every length `1`, the predicate
`IsOneProcessorSchedule` reused from `SequencingToMinimizeWeightedTardinessWanted`), and in a
chain `S_j ≥ S_i + 1 + 1`. Start times are natural numbers: with unit jobs and integer lags,
shifting every job as early as the machine order allows gives an integral schedule with no
later completion times. Binary encoding of all numbers (the problem is NP-complete in the strong
sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The weight `w_j` of job `j`: the `j`-th listed number. -/
def weight (i : SingleMachineChainsTimeLagMakespanInstance) (j : ℕ) : ℕ := i.1.getD j 0

/-- Well-formedness of an instance: well-formed for `1|chains(l)|C_max` (the chains consist of
job indices, and no job occurs twice), and the time lag is `1`. -/
def WellFormed (i : SingleMachineChainsTimeLagMakespanInstance) : Prop :=
  SingleMachineChainsTimeLagMakespan.WellFormed i ∧ i.2.2.1 = 1

/-- Some start times `S` never run two unit jobs at once, start each job in a chain at least the
lag `1` after its immediate predecessor completes, and have total weighted completion time
`Σ_j w_j (S j + 1)` at most `K`. -/
def SingleMachineUnitChainsUnitLagWeightedCompletionFeasible
    (i : SingleMachineChainsTimeLagMakespanInstance) : Prop :=
  ∃ S : ℕ → ℕ,
    IsOneProcessorSchedule (fun _ : Fin i.1.length => 1) (fun j => S j) ∧
    (∀ c ∈ i.2.1, ∀ k, k + 1 < c.length →
      S (c.getD k 0) + 1 + i.2.2.1 ≤ S (c.getD (k + 1) 0)) ∧
    ∑ j ∈ Finset.range i.1.length, weight i j * (S j + 1) ≤ i.2.2.2

open Classical in
/-- `1|chains(1);p_i=1|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def singleMachineUnitChainsUnitLagWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleMachineChainsTimeLagMakespanInstance) x with
  | some i => decide (WellFormed i ∧ SingleMachineUnitChainsUnitLagWeightedCompletionFeasible i)
  | none => false

/-- **`1|chains(1);p_i=1|Σw_iC_i` is NP-complete.** Source: Brucker and Knust (classification
tables), citing Tanaev, Sotskov and Strusevich (1994). -/
public theorem_wanted singleMachineUnitChainsUnitLagWeightedCompletion_npComplete :
    singleMachineUnitChainsUnitLagWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleMachineUnitChainsUnitLagWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.SingleMachineUnitChainsUnitLagWeightedCompletion
