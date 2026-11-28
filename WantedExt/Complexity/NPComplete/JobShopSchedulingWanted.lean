/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOB-SHOP SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP
SCHEDULING (with the definition of one-processor schedules in [SS1]);
M. R. Garey, D. S. Johnson, and R. Sethi, "The complexity of flowshop and
jobshop scheduling", Mathematics of Operations Research 1 (1976), 117-129,
doi:10.1287/moor.1.2.117.
-/
module

public import Batteries.Data.List.Basic
public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.JobShopScheduling

/-!
# JOB-SHOP SCHEDULING is NP-complete

INSTANCE: a number `m ∈ ℤ⁺` of processors, a set `J` of jobs, each job `j ∈ J` consisting of
an ordered collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, for each such task `t` a length
`l(t) ∈ ℤ₀⁺` and a processor `p(t) ∈ {1, 2, …, m}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all
`j ∈ J` and `1 ≤ k < n_j`, and a deadline `D ∈ ℤ⁺`.
QUESTION: is there a job-shop schedule for `J` that meets the overall deadline, i.e., a
collection of one-processor schedules `σᵢ` mapping `{t : p(t) = i}` into `ℤ₀⁺`, `1 ≤ i ≤ m`,
such that `σᵢ(t) > σᵢ(t')` implies `σᵢ(t) ≥ σᵢ(t') + l(t')`, such that
`σ(t_{k+1}[j]) ≥ σ(t_k[j]) + l(t_k[j])` for all `j ∈ J` and `1 ≤ k < n_j`, and such that
`σ(t_{n_j}[j]) + l(t_{n_j}[j]) ≤ D` for all `j ∈ J`?

A one-processor schedule [SS1] is one-to-one. The `σᵢ` have disjoint domains, so they are
represented by one function `σ` on all tasks, required to be one-to-one on the tasks of each
processor. Garey and Johnson print the machine constraint of [SS18] as
"`σᵢ(t) > σᵢ(t')` implies `σᵢ(t) ≥ σᵢ(t') + l(t)`"; that is a misprint for `l(t')`, the
one-processor schedule condition of [SS1] (a task starting later must wait until the earlier
task `t'` finishes), which is what is stated here. Task positions are numbered from `0` below.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **JOB-SHOP SCHEDULING is NP-complete.** Source: Garey and Johnson (1979), [SS18];
Garey, Johnson, and Sethi (1976). -/
public theorem_wanted jobShopScheduling_npComplete :
    jobShopSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L jobShopSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.JobShopScheduling
