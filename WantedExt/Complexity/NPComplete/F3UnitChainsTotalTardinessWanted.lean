/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP `F3|p_ij=1;chains|ΣT_i` is NP-complete

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036; recorded as
strongly NP-hard (a minimal NP-hard problem) in P. Brucker and S. Knust, *Complexity results for
scheduling problems*, class "Flow-shop problems without preemption" (University of Osnabrück,
http://www2.informatik.uni-osnabrueck.de/knust/class/), problem `F3|p_ij=1;chains|ΣT_i`, credited
to Brucker and Knust (1999).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.F3UnitChainsTotalTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.F3UnitChainsTotalTardiness

open F3UnitChainsLateJobs (IsSchedule)

/-!
# FLOW SHOP `F3|p_ij=1;chains|ΣT_i` is NP-complete

There are three machines `M₁, M₂, M₃` in a flow shop and `n` jobs. Each job `i` consists of three
operations `O_i1, O_i2, O_i3` with unit processing times (`p_ij = 1`); `O_ij` is processed on
`M_j`, and `O_i,j+1` cannot start before `O_ij` is completed. Each machine processes at most one
operation at a time. The jobs are subject to precedence constraints forming chains (every job
has at most one immediate predecessor and at most one immediate successor): if `i` precedes `j`,
then `j` cannot start before `i` is completed. `C_i` is the completion time of the last operation
of job `i`. Each job has a due date `d_i` and tardiness `T_i = max(0, C_i - d_i)`. Given an
integer `K`, the question is whether some feasible schedule has total tardiness `ΣT_i ≤ K`.

The instance, its well-formedness (the arcs form chains) and the schedule predicate are those of
`F3UnitChainsLateJobsWanted` (`F3|p_ij=1;chains|ΣU_i`). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FLOW SHOP `F3|p_ij=1;chains|ΣT_i` is NP-complete.** Source: Brucker and Knust (1999),
as recorded in the Brucker-Knust classification of scheduling problems. -/
public theorem_wanted f3UnitChainsTotalTardiness_npComplete :
    f3UnitChainsTotalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L f3UnitChainsTotalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.F3UnitChainsTotalTardiness
