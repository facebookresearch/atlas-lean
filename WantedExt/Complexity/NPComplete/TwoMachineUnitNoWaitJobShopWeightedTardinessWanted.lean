/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP, TOTAL WEIGHTED TARDINESS, is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class table "Job-shop problems with nowait" (`J2|p_ij=1;no-wait|∑ w_iT_i`: minimal NP-hard,
in the strong sense, Timkovsky (1998)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopWeightedTardiness

/-!
# TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP, TOTAL WEIGHTED TARDINESS, is NP-complete

INSTANCE: a job shop with `m = 2` machines `M_1, M_2` and jobs `1, …, n`; job `j` is a chain of
`n_j` operations `O_j1, …, O_jn_j`, where `O_jk` is processed on machine `μ_jk` for
`p_jk = 1` time unit, consecutive operations of a job use different machines, and `O_j,k+1`
cannot start before `O_jk` is completed; each machine processes at most one operation at a
time; no wait: each operation of a job starts exactly when the preceding operation of the same
job is completed; each job `j` has a due date `d_j ∈ ℤ₀⁺` and a weight `w_j ∈ ℤ₀⁺`; and a bound
`K`.
QUESTION: is there a feasible schedule whose total weighted tardiness
`∑_j w_j max(0, C_j - d_j)` is at most `K`, where `C_j` is the completion time of the last
operation of job `j`?

In the Brucker-Knust notation this is `J2|p_ij=1;no-wait|∑ w_iT_i`. With two machines and
consecutive operations on different machines, the machines of a job alternate, so job `j` is given
by the machine `μ_j1 ∈ {1, 2}` of its first operation and its number `n_j ≥ 1` of operations; `n_j`
is a number of the input, written in binary like the due dates, the weights and `K`. This is the
convention of the Brucker-Knust classification of unit-time job shops, which lists
`J2|p_ij=1;no-wait|C_max` both as pseudopolynomially solvable and as NP-hard in the ordinary sense;
with unit processing times this is possible only with the operation counts written in binary. Under
the no-wait condition a schedule is determined by the start times `S_j` of the jobs' first
operations, and two jobs use the same machine at the same time exactly when their intervals
`[S_j, S_j + n_j)` overlap and `μ_j1 + S_j` and `μ_j'1 + S_j'` have the same parity, so the problem
is in NP with this encoding.

Operations are numbered from `0`; operation `k` of job `j` is processed on `μ_j1` if `k` is even
and on the other machine if `k` is odd. An operation started at time `s` occupies its machine
during `[s, s + 1)`. The precedence condition `σ(O_j,k+1) ≥ σ(O_jk) + 1` is implied by the
no-wait equality `σ(O_j,k+1) = σ(O_jk) + 1` and is not stated separately. The tardiness
`max(0, C_j - d_j)` is the truncated subtraction `C_j - d_j` on `ℕ`. The bound `K` is a natural
number (the objective is nonnegative).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP, TOTAL WEIGHTED TARDINESS, is
NP-complete.** Source: Timkovsky (1998); Brucker and Knust, class table "Job-shop problems with
nowait". -/
public theorem_wanted twoMachineUnitNoWaitJobShopWeightedTardiness_npComplete :
    twoMachineUnitNoWaitJobShopWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineUnitNoWaitJobShopWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopWeightedTardiness
