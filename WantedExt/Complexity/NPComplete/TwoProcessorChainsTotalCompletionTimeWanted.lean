/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR CHAINS SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME is NP-complete

Source:
J. Du, J. Y.-T. Leung and G. H. Young, "Scheduling chain-structured tasks to minimize makespan
and mean flow time", Information and Computation 92 (1991), 219-236,
doi:10.1016/0890-5401(91)90009-Q;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 5.3 (`P2|chains|∑Cᵢ`,
NP-hard in the strong sense, Du et al.).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TwoProcessorTreePrecedenceCompletionTimeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorChainsTotalCompletionTime

open TwoProcessorTreePrecedenceCompletionTime
  (TwoProcessorTreePrecedenceCompletionTimeInstance IsInTree IsOutTree
    TwoProcessorTreePrecedenceCompletionTimeFeasible)

/-!
# TWO-PROCESSOR CHAINS SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME is NP-complete

This is `P2|chains|∑Cᵢ` in the notation of Brucker's *Scheduling Algorithms*.

INSTANCE: `m = 2` identical parallel processors, each processing at most one job at a time; jobs
`1, …, n`, job `i` with a processing time `pᵢ ∈ ℤ⁺`; precedence constraints that form a set of
chains (every job has at most one immediate predecessor and at most one immediate successor),
where `i` preceding `j` means that `j` cannot start before `i` is completed; and an integer `K`.
QUESTION: is there a nonpreemptive schedule whose total completion time `∑ᵢ Cᵢ` is at most `K`,
`Cᵢ` being the completion time of job `i`?

Du, Leung and Young prove that minimizing the mean flow time of a set of chains on `m`
identical processors is NP-hard in the strong sense for every fixed `m > 1`; with all jobs
available at time `0` the mean flow time is `(∑ᵢ Cᵢ) / n`. Brucker's Table 5.3 lists
`P2|chains|∑Cᵢ` as NP-hard in the strong sense, citing them.

The problem is the restriction of the two-processor tree-precedence problem of
`WantedExt.Complexity.NPComplete.TwoProcessorTreePrecedenceCompletionTimeWanted` (equal
weights, an in-tree or an out-tree) to unit weights and to orders that are both an in-tree and
an out-tree: its instance, its well-formedness (`m = 2`, positive lengths and weights, equal
weights, `0 < K`, listed pairs that name tasks and form a strict partial order, and its
immediate-predecessor relation) and its question (a 2-processor schedule, start times in `ℤ₀⁺`,
obeying the precedence constraints with weighted completion time at most `K`) are reused
unchanged. The order is a set of chains exactly when every task has at most one immediate
successor (`IsInTree`) and at most one immediate predecessor (`IsOutTree`); with every weight
`1`, the weighted completion time is `∑ᵢ Cᵢ`. Integral start times lose no generality, since
the data are integers. The positive bound `K` excludes only the empty instance with `K = 0`.
Binary encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is well-formed for the two-processor tree-precedence
problem (`m = 2`, positive lengths and equal positive weights, `0 < K`, the listed pairs name
tasks and form a strict partial order), the order is a set of chains (at most one immediate
successor and at most one immediate predecessor per task), and every weight is `1`. -/
def WellFormed (i : TwoProcessorTreePrecedenceCompletionTimeInstance) : Prop :=
  TwoProcessorTreePrecedenceCompletionTime.WellFormed i ∧ IsInTree i ∧ IsOutTree i ∧
    ∀ p ∈ i.2.1, p.2 = 1

open Classical in
/-- TWO-PROCESSOR CHAINS SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME as a decision problem
over bitstrings. -/
noncomputable def twoProcessorChainsTotalCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTreePrecedenceCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTreePrecedenceCompletionTimeFeasible i)
  | none => false

/-- **TWO-PROCESSOR CHAINS SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME (`P2|chains|∑Cᵢ`) is
NP-complete.** Source: Du, Leung and Young (1991); Brucker (2007), Table 5.3. -/
public theorem_wanted twoProcessorChainsTotalCompletionTime_npComplete :
    twoProcessorChainsTotalCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorChainsTotalCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorChainsTotalCompletionTime
