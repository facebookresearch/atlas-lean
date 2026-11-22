/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP `O2|p_ij=1;chains;no-wait|Σw_iC_i` is NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1; recorded as strongly NP-hard (a minimal NP-hard problem) in P.
Brucker and S. Knust, *Complexity results for scheduling problems*, class "Open-shop problems with
nowait" (University of Osnabrück, http://www2.informatik.uni-osnabrueck.de/knust/class/), problem
`O2|p_ij=1;chains;no-wait|Σw_iC_i`, credited to Timkovsky (2003).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.F3UnitChainsWeightedCompletionWanted
public import WantedExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.O2UnitChainsNoWaitWeightedCompletion

open F3UnitChainsWeightedCompletion (F3UnitChainsWeightedCompletionInstance WellFormed)
open UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-!
# NO-WAIT OPEN SHOP `O2|p_ij=1;chains;no-wait|Σw_iC_i` is NP-complete

There are two machines `M₁, M₂` in an open shop and `n` jobs. Each job `i` consists of two
operations `O_i1, O_i2` with unit processing times (`p_ij = 1`); `O_ij` is processed on `M_j`, and
the two operations of a job may be processed in either order, but not at the same time. Each machine
processes at most one operation at a time. The jobs are subject to precedence constraints forming
chains (every job has at most one immediate predecessor and at most one immediate successor): if `i`
precedes `j`, then no operation of `j` starts before every operation of `i` is completed. No wait:
the second operation of each job starts exactly when its first operation is completed. Each job has
a weight `w_i`, and `C_i` is the completion time of its last operation. Given an integer `K`, the
question is whether some feasible schedule has total weighted completion time at most `K`
(`Σw_iC_i ≤ K`).

The instance (weights, chain arcs, bound) and its well-formedness (the arcs form chains) are those
of the flow shop `F3|p_ij=1;chains|Σw_iC_i` (`F3UnitChainsWeightedCompletionWanted`); only the
machine environment differs. The schedule predicate is the unit-time open-shop schedule
`IsUnitOpenShopSchedule` of `UnitOpenShopOutTreeMaxLatenessWanted` with two machines: `σ k j` is the
start time of the operation of job `j` on machine `k` (`0, 1` for `M₁, M₂`); the operations on a
machine, and the two operations of a job, start at different times; and if the arc `(i, j)` is
given, every operation of `j` starts after every operation of `i` is completed. The no-wait
condition is `σ 0 j + 1 = σ 1 j ∨ σ 1 j + 1 = σ 0 j` for every job `j`. Time is discrete: with unit
operations and integer data, rounding the start times of any schedule down keeps every constraint
and increases no completion time. Binary encoding of all numbers.

Brucker and Knust classify the problem as strongly NP-hard, crediting Timkovsky (2003), whose full
text was not available. Membership in NP is the certificate argument: moving every operation that
starts after an idle time slot (one in which no operation runs) one unit earlier keeps every
constraint and increases no completion time, so some optimal schedule has all `2n` start times below
`2n`, and they are checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some two-machine unit-time open-shop schedule `σ` obeying the chain arcs
(`IsUnitOpenShopSchedule 2`) in which every job runs its two operations back to back has total
weighted completion time at most `K`, with `C_j = max (σ 0 j) (σ 1 j) + 1`. -/
def O2UnitChainsNoWaitWeightedCompletionFeasible
    (i : F3UnitChainsWeightedCompletionInstance) : Prop :=
  ∃ σ : Fin 2 → Fin i.1.length → ℕ, IsUnitOpenShopSchedule 2 i.1.length i.2.1 σ ∧
    (∀ j, σ 0 j + 1 = σ 1 j ∨ σ 1 j + 1 = σ 0 j) ∧
    ∑ j, i.1.get j * (max (σ 0 j) (σ 1 j) + 1) ≤ i.2.2

open Classical in
/-- `O2|p_ij=1;chains;no-wait|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def o2UnitChainsNoWaitWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ O2UnitChainsNoWaitWeightedCompletionFeasible i)
  | none => false

/-- **NO-WAIT OPEN SHOP `O2|p_ij=1;chains;no-wait|Σw_iC_i` is NP-complete.** Source: Timkovsky
(2003), as recorded in the Brucker-Knust classification of scheduling problems. -/
public theorem_wanted o2UnitChainsNoWaitWeightedCompletion_npComplete :
    o2UnitChainsNoWaitWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L o2UnitChainsNoWaitWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.O2UnitChainsNoWaitWeightedCompletion
