/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST with costs in {-1, 0, 1} is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS7] SEQUENCING TO MINIMIZE
MAXIMUM CUMULATIVE COST, p. 238 (comment: "Remains NP-complete even if `c(t) ∈ {-1, 0, 1}` for
all `t ∈ T`"; reference: [Abdel-Wahab, 1976], transformation from REGISTER SUFFICIENCY);
H. M. Abdel-Wahab, *Scheduling with Applications to Register Allocation and Deadlock Problems*,
Ph.D. thesis, University of Waterloo (1976) (not available to this formalization).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCostWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCostTernaryCosts

open MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCost
  (SequencingToMinimizeMaximumCumulativeCostInstance Task cost
    SequencingToMinimizeMaximumCumulativeCostFeasible)

/-!
# SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST with costs in {-1, 0, 1} is NP-complete

INSTANCE: a set `T` of tasks, a partial order `<` on `T`, a "cost" `c(t) ∈ {-1, 0, 1}` for each
`t ∈ T`, and a constant `K ∈ ℤ`.
QUESTION: is there a one-processor schedule `σ` for `T` that obeys the precedence constraints
and which has the property that, for every task `t ∈ T`, the sum of the costs for all tasks `t'`
with `σ(t') ≤ σ(t)` is at most `K`?

This is the restriction of SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST
(`SequencingToMinimizeMaximumCumulativeCostWanted`, GJ [SS7]) stated in the entry's comment. The
instance type, `SequencingToMinimizeMaximumCumulativeCost.WellFormed` (the listed pairs name tasks
and form a strict partial order) and `SequencingToMinimizeMaximumCumulativeCostFeasible` are the
parent's, unchanged; `WellFormed` adds that every cost `c(t)` (the integer `p - q` of its pair
`(p, q)`) is `-1`, `0` or `1`. Garey and Johnson give the comment without a separate citation;
the entry's reference is Abdel-Wahab's thesis.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST
instance in which every cost is `-1`, `0` or `1`. -/
def WellFormed (i : SequencingToMinimizeMaximumCumulativeCostInstance) : Prop :=
  SequencingToMinimizeMaximumCumulativeCost.WellFormed i ∧
    ∀ t : Task i, cost i t = -1 ∨ cost i t = 0 ∨ cost i t = 1

open Classical in
/-- SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST with costs in `{-1, 0, 1}` as a decision
problem over bitstrings. -/
noncomputable def sequencingToMinimizeMaximumCumulativeCostTernaryCostsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SequencingToMinimizeMaximumCumulativeCostInstance) x with
  | some i => decide (WellFormed i ∧ SequencingToMinimizeMaximumCumulativeCostFeasible i)
  | none => false

/-- **SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST is NP-complete with costs in `{-1, 0, 1}`.**
Source: Garey and Johnson (1979), [SS7], comment; Abdel-Wahab (1976). -/
public theorem_wanted sequencingToMinimizeMaximumCumulativeCostTernaryCosts_npComplete :
    sequencingToMinimizeMaximumCumulativeCostTernaryCostsDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sequencingToMinimizeMaximumCumulativeCostTernaryCostsDec

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCostTernaryCosts
