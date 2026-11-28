/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROJECT SCHEDULING WITH RESOURCES AND TIME WINDOWS: FEASIBILITY is NP-complete

Source:
M. Bartusch, R. H. Möhring and F. J. Radermacher, "Scheduling project networks with resource
constraints and time windows", Annals of Operations Research 16 (1988), 201-240,
doi:10.1007/BF02283745;
S. Hartmann and D. Briskorn, "A survey of variants and extensions of the resource-constrained
project scheduling problem", European Journal of Operational Research 207 (2010), 1-14,
doi:10.1016/j.ejor.2009.11.005, Section 3.2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RcpspTimeWindowsFeasibilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RcpspTimeWindowsFeasibility

/-!
# PROJECT SCHEDULING WITH RESOURCES AND TIME WINDOWS: FEASIBILITY is NP-complete

INSTANCE: activities `1, …, J` with integer durations `p_j ≥ 0`; renewable resources
`1, …, K` with capacities `R_k`, activity `j` requiring `r_{jk}` units of resource `k` in
every period in which it is in process; and time lags `(i, j, δ_{ij})` with integer
`δ_{ij}`, each requiring `S_j - S_i ≥ δ_{ij}` of the start times. A minimal start-to-start
time lag `d` from `i` to `j` is the lag `(i, j, d)`; a maximal one is the lag `(j, i, -d)`.
QUESTION: are there integer start times `S_j ≥ 0` satisfying all time lags such that in every
period `t`, for every resource `k`, the activities in process (`S_j ≤ t < S_j + p_j`) require
at most `R_k` units in total?

This is the feasibility problem of the resource-constrained project scheduling problem with
minimal and maximal time lags (RCPSP/max); Bartusch, Möhring and Radermacher prove it
NP-complete (as recorded by Hartmann and Briskorn). Membership in NP: fixing the order of all
start and completion events of a feasible schedule turns the constraints into a system of
difference constraints with small integer bounds, whose solutions keep the same activities in
process together, so a feasible instance has a feasible schedule with start times of
polynomial bit size.
Activities and resources are numbered from `0` below; all numbers use the canonical binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PROJECT SCHEDULING WITH RESOURCES AND TIME WINDOWS: FEASIBILITY is NP-complete.**
Source: Bartusch, Möhring and Radermacher (1988); Hartmann and Briskorn (2010). -/
public theorem_wanted rcpspTimeWindowsFeasibility_npComplete :
    rcpspTimeWindowsFeasibilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rcpspTimeWindowsFeasibilityDec

end MetaMathlibExt.Complexity.NPComplete.RcpspTimeWindowsFeasibility
