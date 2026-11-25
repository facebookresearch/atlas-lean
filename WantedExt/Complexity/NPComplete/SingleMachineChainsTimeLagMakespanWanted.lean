/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE SCHEDULING WITH TIME LAGS `1|chains(l)|Cmax` is NP-complete

Source:
E. D. Wikum, D. C. Llewellyn, and G. L. Nemhauser, "One-machine generalized precedence
constrained scheduling problems", Operations Research Letters 16(2) (1994), 87-99,
doi:10.1016/0167-6377(94)90064-7; recorded as strongly NP-hard in P. Brucker and S. Knust,
*Complexity results for scheduling problems*, class "Single machine problems with non-negative
time-lags" (University of Osnabrück), minimal NP-hard problem `1|chains(l)|Cmax`.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleMachineChainsTimeLagMakespan

/-!
# SINGLE-MACHINE SCHEDULING WITH TIME LAGS `1|chains(l)|Cmax` is NP-complete

INSTANCE: one machine that processes at most one job at a time; jobs `1, …, n` with nonnegative
integer processing times `p_i`; a precedence relation consisting of disjoint chains (each job has
at most one immediate predecessor and at most one immediate successor), every precedence pair
`i → j` carrying the same finish-start time lag `l`, i.e. `S_j ≥ C_i + l`; and an integer bound
`K`.
QUESTION: is there a feasible schedule with makespan `max_i C_i ≤ K`, where `S_i` is the start
and `C_i = S_i + p_i` the completion time of job `i`?

Jobs are the indices `0, …, n - 1` of the list of processing times. The chains are lists of job
indices; consecutive jobs in a chain are an immediate predecessor and successor. No job is in two
chains or twice in a chain, so each job has at most one immediate predecessor and one immediate
successor; jobs in no chain are unconstrained. Jobs are not preempted; a schedule gives every job
a start time `S j ≥ 0`, and two jobs never overlap: one completes before the other starts. Numbers
are in binary; Brucker and Knust list the problem as NP-hard in the strong sense.

In Brucker and Knust's notation the lag annotation distinguishes three cases: `(l)` is one lag
`l` shared by all precedence pairs, `(l_ij)` allows a different lag on each pair, and `(1)` is the
unit lag. Their table for single machine problems with non-negative time lags lists
`1|chains(l)|Cmax` (Wikum et al. 1994) as minimal NP-hard next to `1|chains(l_ij); p_i = 1|Cmax`
(Yu 1996) and `1|prec(l); p_i = 1|Cmax` (Leung et al. 1984), and lists `1|chains(l); p_i = p|Cmax`
and `1|prec(1)|Cmax` as polynomially solvable; the problem here is the common-lag case `(l)`, as in
the campaign record.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **`1|chains(l)|Cmax` is NP-complete.** Source: Wikum, Llewellyn, and Nemhauser (1994); Brucker
and Knust. -/
public theorem_wanted singleMachineChainsTimeLagMakespan_npComplete :
    singleMachineChainsTimeLagMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleMachineChainsTimeLagMakespanDec

end MetaMathlibExt.Complexity.NPComplete.SingleMachineChainsTimeLagMakespan
