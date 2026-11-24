/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE CHAINS WITH CONSTANT TIME LAGS AND TOTAL COMPLETION TIME is NP-complete

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(online tables), class "Single machine problems with non-negative time-lags" (lists
`1|chains(l)|ΣCᵢ` as minimal strongly NP-hard, citing Brucker and Knust (1999)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleMachineChainsTimeLagsTotalCompletion

/-!
# SINGLE-MACHINE CHAINS WITH CONSTANT TIME LAGS AND TOTAL COMPLETION TIME is NP-complete

INSTANCE: a single machine that processes at most one job at a time; jobs with processing times
`pⱼ ∈ ℤ₀⁺`, partitioned into chains (each job has at most one immediate predecessor and at most
one immediate successor); a time lag `l ∈ ℤ₀⁺`; and a bound `K ∈ ℤ₀⁺`. Whenever job `i` is the
immediate predecessor of job `j` in a chain, `j` may start only `l` time units after `i` is
finished: `Sⱼ ≥ Cᵢ + l` (a positive finish-start time lag). QUESTION: is there a feasible
schedule whose total completion time `Σⱼ Cⱼ` is at most `K`?

This is the decision version of `1|chains(l)|ΣCᵢ`. The chains are listed, each as the list of
processing times of its jobs in chain order; a chain of one job is an unconstrained job.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the chains (chain `c` is the list of processing times of its jobs, in chain
order), the time lag `l`, and the bound `K`. Job `(c, k)` is the `k`-th job of chain `c`. -/
abbrev SingleMachineChainsTimeLagsTotalCompletionInstance := List (List ℕ) × ℕ × ℕ

/-- The processing time of job `(c, k)`. -/
def ptime (i : SingleMachineChainsTimeLagsTotalCompletionInstance) (c k : ℕ) : ℕ :=
  (i.1.getD c []).getD k 0

/-- The number of jobs in chain `c`. -/
def chainLength (i : SingleMachineChainsTimeLagsTotalCompletionInstance) (c : ℕ) : ℕ :=
  (i.1.getD c []).length

/-- Well-formedness of an instance: every chain has at least one job. -/
def WellFormed (i : SingleMachineChainsTimeLagsTotalCompletionInstance) : Prop :=
  ∀ c ∈ i.1, c ≠ []

/-- A schedule with total completion time at most `K`: start times `S c k` such that the
machine processes one job at a time, consecutive jobs of a chain respect the time lag, and the
completion times `S c k + p_{c,k}` sum to at most `K`. -/
def SingleMachineChainsTimeLagsTotalCompletionFeasible
    (i : SingleMachineChainsTimeLagsTotalCompletionInstance) : Prop :=
  ∃ S : ℕ → ℕ → ℕ,
    (∀ c < i.1.length, ∀ k < chainLength i c, ∀ c' < i.1.length, ∀ k' < chainLength i c',
      (c, k) ≠ (c', k') →
        S c k + ptime i c k ≤ S c' k' ∨ S c' k' + ptime i c' k' ≤ S c k) ∧
    (∀ c < i.1.length, ∀ k, k + 1 < chainLength i c →
      S c k + ptime i c k + i.2.1 ≤ S c (k + 1)) ∧
    (Finset.range i.1.length).sum (fun c =>
      (Finset.range (chainLength i c)).sum (fun k => S c k + ptime i c k)) ≤ i.2.2

open Classical in
/-- SINGLE-MACHINE CHAINS WITH CONSTANT TIME LAGS AND TOTAL COMPLETION TIME as a decision problem
over bitstrings. -/
noncomputable def singleMachineChainsTimeLagsTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleMachineChainsTimeLagsTotalCompletionInstance) x with
  | some i => decide (WellFormed i ∧ SingleMachineChainsTimeLagsTotalCompletionFeasible i)
  | none => false

/-- **SINGLE-MACHINE CHAINS WITH CONSTANT TIME LAGS AND TOTAL COMPLETION TIME is NP-complete.**
Source: Brucker and Knust (1999); Brucker and Knust (classification tables). -/
public theorem_wanted singleMachineChainsTimeLagsTotalCompletion_npComplete :
    singleMachineChainsTimeLagsTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleMachineChainsTimeLagsTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.SingleMachineChainsTimeLagsTotalCompletion
