/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP `F3|p_ij=1;chains|Σw_iC_i` is NP-complete

Source:
V. S. Tanaev, Y. N. Sotskov and V. A. Strusevich, *Scheduling Theory. Multi-Stage Systems*,
Mathematics and its Applications 285, Kluwer Academic Publishers, Dordrecht (1994),
doi:10.1007/978-94-011-1192-8; recorded as strongly NP-hard (a minimal NP-hard problem) in
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Flow-shop problems
without preemption" (University of Osnabrück,
http://www2.informatik.uni-osnabrueck.de/knust/class/), problem `F3|p_ij=1;chains|Σw_iC_i`,
credited to Tanaev et al. (1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.F3UnitChainsWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.F3UnitChainsWeightedCompletion

open F3UnitChainsLateJobs (ChainsWellFormed IsSchedule)

/-!
# FLOW SHOP `F3|p_ij=1;chains|Σw_iC_i` is NP-complete

There are three machines `M₁, M₂, M₃` in a flow shop and `n` jobs. Each job `i` consists of three
operations `O_i1, O_i2, O_i3` with unit processing times (`p_ij = 1`); `O_ij` is processed on
`M_j`, and `O_i,j+1` cannot start before `O_ij` is completed. Each machine processes at most one
operation at a time. The jobs are subject to precedence constraints forming chains (every job
has at most one immediate predecessor and at most one immediate successor): if `i` precedes `j`,
then `j` cannot start before `i` is completed. `C_i` is the completion time of the last operation
of job `i`. Each job has a weight `w_i`. Given an integer `K`, the question is whether some
feasible schedule has total weighted completion time `Σw_iC_i ≤ K`.

The chain conditions and the schedule predicate are those of `F3UnitChainsLateJobsWanted`
(`F3|p_ij=1;chains|ΣU_i`). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FLOW SHOP `F3|p_ij=1;chains|Σw_iC_i` is NP-complete.** Source: Tanaev, Sotskov and
Strusevich (1994), as recorded in the Brucker-Knust classification of scheduling problems. -/
public theorem_wanted f3UnitChainsWeightedCompletion_npComplete :
    f3UnitChainsWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L f3UnitChainsWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.F3UnitChainsWeightedCompletion
