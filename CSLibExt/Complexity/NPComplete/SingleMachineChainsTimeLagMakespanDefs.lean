/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE SCHEDULING WITH TIME LAGS `1|chains(l)|Cmax`: definitions

Source:
E. D. Wikum, D. C. Llewellyn, and G. L. Nemhauser, "One-machine generalized precedence
constrained scheduling problems", Operations Research Letters 16(2) (1994), 87-99,
doi:10.1016/0167-6377(94)90064-7; recorded as strongly NP-hard in P. Brucker and S. Knust,
*Complexity results for scheduling problems*, class "Single machine problems with non-negative
time-lags" (University of Osnabrück), minimal NP-hard problem `1|chains(l)|Cmax`.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleMachineChainsTimeLagMakespan

/-- An instance: processing times `p`, chains of job indices, time lag `l`, and bound `K`. -/
abbrev SingleMachineChainsTimeLagMakespanInstance := List ℕ × List (List ℕ) × ℕ × ℕ

/-- The processing time of job `j`. -/
def pt (i : SingleMachineChainsTimeLagMakespanInstance) (j : ℕ) : ℕ := i.1.getD j 0

/-- Well-formedness of an instance: the chains consist of job indices, and no job occurs twice
(in one chain or in two chains), so the chains are disjoint. -/
def WellFormed (i : SingleMachineChainsTimeLagMakespanInstance) : Prop :=
  i.2.1.flatten.Nodup ∧ ∀ j ∈ i.2.1.flatten, j < i.1.length

/-- Some start times `S` complete every job by `K`, never run two jobs at once, and start each
job in a chain at least `l` after its immediate predecessor completes. -/
def SingleMachineChainsTimeLagMakespanFeasible
    (i : SingleMachineChainsTimeLagMakespanInstance) : Prop :=
  ∃ S : ℕ → ℕ,
    (∀ j < i.1.length, S j + pt i j ≤ i.2.2.2) ∧
    (∀ a < i.1.length, ∀ b < i.1.length, a ≠ b →
      S a + pt i a ≤ S b ∨ S b + pt i b ≤ S a) ∧
    ∀ c ∈ i.2.1, ∀ k, k + 1 < c.length →
      S (c.getD k 0) + pt i (c.getD k 0) + i.2.2.1 ≤ S (c.getD (k + 1) 0)

open Classical in
/-- `1|chains(l)|Cmax` as a decision problem over bitstrings. -/
noncomputable def singleMachineChainsTimeLagMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleMachineChainsTimeLagMakespanInstance) x with
  | some i => decide (WellFormed i ∧ SingleMachineChainsTimeLagMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SingleMachineChainsTimeLagMakespan
