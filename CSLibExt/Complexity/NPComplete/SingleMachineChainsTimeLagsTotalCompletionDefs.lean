/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE CHAINS WITH CONSTANT TIME LAGS AND TOTAL COMPLETION TIME: definitions

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(online tables), class "Single machine problems with non-negative time-lags" (lists
`1|chains(l)|ΣCᵢ` as minimal strongly NP-hard, citing Brucker and Knust (1999)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleMachineChainsTimeLagsTotalCompletion

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

end MetaMathlibExt.Complexity.NPComplete.SingleMachineChainsTimeLagsTotalCompletion
