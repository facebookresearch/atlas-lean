/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIXED-INTERVAL SCHEDULING ON ELIGIBLE MACHINES is NP-complete

Source:
E. M. Arkin and E. B. Silverberg, "Scheduling jobs with fixed start and end times", Discrete
Applied Mathematics 18 (1987), 1-8, doi:10.1016/0166-218X(87)90037-0;
D. Hermelin, Y. Itzhaki, H. Molter, and D. Shabtay, "Hardness of interval scheduling on
unrelated machines", arXiv:2206.12825 (2022), Sections 1-2 (problem definition, and the
statement that Arkin and Silverberg proved the problem strongly NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FixedIntervalSchedulingEligibleMachinesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedIntervalSchedulingEligibleMachines

/-!
# FIXED-INTERVAL SCHEDULING ON ELIGIBLE MACHINES is NP-complete

INSTANCE: `m` machines `0, …, m - 1`, each processing at most one job at a time; `n` jobs, job
`j` with integer start time `s_j` and finish time `f_j` (`s_j < f_j`), a weight `w_j ∈ ℤ₀⁺`, and
a set `M_j ⊆ {0, …, m - 1}` of eligible machines; a bound `W`. QUESTION: is there a schedule
`σ` mapping each job to a machine of its `M_j` or to no machine (the job is rejected), such that
no two jobs mapped to the same machine have overlapping intervals, and the total weight of the
scheduled jobs is at least `W`?

This is Interval Scheduling on Eligible Machines (`P | M_j | ∑ w_j E_j`) as defined by Hermelin,
Itzhaki, Molter, and Shabtay (2022, Section 2), in decision form; they record that Arkin and
Silverberg (1987) proved it strongly NP-hard (it is polynomial when every `M_j` is the set of
all machines). Hermelin et al. give job `j` the interval `(d_j - p_j, d_j]`; here a job is given
by its endpoints `s_j = d_j - p_j` and `f_j = d_j`, and two jobs conflict when their intervals
intersect, i.e. `s_j < f_{j'}` and `s_{j'} < f_j` (a job may start when another one finishes).
Times are naturals: shifting all times by a constant changes nothing. `M_j` is given as a list
of machine indices; repeated entries are harmless.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FIXED-INTERVAL SCHEDULING ON ELIGIBLE MACHINES is NP-complete.** Source: Arkin and
Silverberg (1987); Hermelin, Itzhaki, Molter, and Shabtay (2022). -/
public theorem_wanted fixedIntervalSchedulingEligibleMachines_npComplete :
    fixedIntervalSchedulingEligibleMachinesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L fixedIntervalSchedulingEligibleMachinesDec

end MetaMathlibExt.Complexity.NPComplete.FixedIntervalSchedulingEligibleMachines
