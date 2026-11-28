/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COUPLED-TASK SCHEDULING is NP-complete

Source:
A. J. Orman and C. N. Potts, "On the complexity of coupled-task scheduling", Discrete Applied
Mathematics 72 (1997), 141-154, doi:10.1016/S0166-218X(96)00041-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CoupledTaskSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoupledTaskScheduling

/-!
# COUPLED-TASK SCHEDULING is NP-complete

The problem `1 | (a_j, L_j, b_j) | C_max` of Orman and Potts (1997). A coupled-task job `j`
consists of two operations that must be processed on a single machine in a fixed order: a
first operation of length `a_j`, and a second operation of length `b_j` that starts exactly
`L_j` time units after the first one completes. The machine processes at most one operation at
a time; operations of other jobs may be processed during the delay `L_j`. Given a bound `K`,
the question is whether there is a schedule of all jobs with makespan at most `K`.

Operation lengths `a_j`, `b_j` are positive integers and delays `L_j` are nonnegative
integers, all in binary encoding. Orman and Potts prove the problem strongly NP-hard, already
for special cases in which two of the three parameters are common to all jobs; NP membership
holds because start times bounded by `K` form a polynomial-size certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COUPLED-TASK SCHEDULING is NP-complete.** Source: Orman and Potts (1997). -/
public theorem_wanted coupledTaskScheduling_npComplete :
    coupledTaskSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coupledTaskSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.CoupledTaskScheduling
