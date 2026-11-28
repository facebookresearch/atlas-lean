/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEADLOCK POTENTIAL is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4(3)
(1983), 286-300, doi:10.1016/0196-6774(83)90028-7, problem DEADLOCK POTENTIAL;
T. Minoura, "Deadlock avoidance revisited", Journal of the ACM 29(4) (1982), 1023-1048,
doi:10.1145/322344.322351.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DeadlockPotentialDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeadlockPotential

/-!
# DEADLOCK POTENTIAL is NP-complete

The model of Johnson's column (Sept. 1983, Section 2). There are resources `R₁, …, R_m` with
integer bounds `B₁, …, B_m`. A (straight-line) process is a sequence of steps; each step `v` has
a resource allocation vector `a(v) = ⟨a₁(v), …, a_m(v)⟩` of integers (a positive entry allocates
units of the resource to the process, a negative one returns units to the common pool). A
partial schedule `S = ⟨u₁, …, u_T⟩` interleaves a prefix of each process. It is legal if
`0 ≤ Σ_{i=1}^{t} a_j(u_i) ≤ B_j` for every `j` and every `t`, `1 ≤ t ≤ T`; each process is
legal, i.e. the partial schedule consisting of that process alone is legal. A legal partial
schedule is deadlocked if (a) some process is not entirely contained in it, and (b) for each
such process, the first step `v` not in the schedule satisfies `a_j(v) + Σ_{i=1}^{T} a_j(u_i) >
B_j` for some `j`.

INSTANCE: resources with integer bounds, a set of legal processes with their allocation vectors,
and a legal partial schedule `S`. QUESTION: can `S` be extended to a deadlocked schedule, i.e. is
there a deadlocked schedule that has `S` as a prefix?

Representation: resources are `0, …, m - 1` (`m` the length of the bound list) and processes
`0, …, P - 1`. A process is a list of steps, a step a list of `m` integers, each given as a pair
`(positive part, negative part)` of natural numbers (`a_j(v) = pos - neg`). A partial schedule
is a list of process indices: the `k`-th occurrence of `p` stands for the `k`-th step of `p`
(counting from `0`), so the step at position `t` is step `(σ.take t).count σ[t]` of process
`σ[t]`, and process `p` has executed its first `σ.count p` steps. Numbers use the canonical
binary encoding; Minoura's transformation is from 3SAT, and the column notes the problem is
NP-complete even for the empty partial schedule.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DEADLOCK POTENTIAL is NP-complete.** Source: Johnson (1983), NP-completeness column;
Minoura (1982). -/
public theorem_wanted deadlockPotential_npComplete :
    deadlockPotentialDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L deadlockPotentialDec

end MetaMathlibExt.Complexity.NPComplete.DeadlockPotential
