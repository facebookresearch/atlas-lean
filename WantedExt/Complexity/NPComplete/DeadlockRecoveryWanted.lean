/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEADLOCK RECOVERY is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4(3)
(1983), 286-300, doi:10.1016/0196-6774(83)90028-7, problem DEADLOCK RECOVERY, as corrected in
the column of Journal of Algorithms 5(1) (1984), 147-160, doi:10.1016/0196-6774(84)90045-2;
J. Y.-T. Leung and E. K. Lai, "On minimum cost recovery from system deadlock", IEEE Transactions
on Computers C-28(9) (1979), 671-677, doi:10.1109/TC.1979.1675435.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DeadlockRecoveryDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeadlockRecovery

/-!
# DEADLOCK RECOVERY is NP-complete

INSTANCE (Johnson, Sept. 1983): a set `{R₁, …, R_m}` of resources with integer resource bounds
`B₁, …, B_m`, a set `P` of blocked processes, each process `p` having a non-negative integer cost
`c(p)`, a vector `r(p)` of currently allocated resource amounts, and a vector `a(p)` of current
requests satisfying (a) `r_j(p) + a_j(p) ≤ B_j` for `1 ≤ j ≤ m`, and (b) for some `j`,
`a_j(p) + Σ_{p ∈ P} r_j(p) > B_j`, and an overall cost bound `K`.

QUESTION (as corrected in the March 1984 column): is there a subset `P' ⊆ P` with
`Σ_{p ∈ P'} c(p) ≤ K` such that, if all processes in `P'` are aborted and their resources
returned to the common pool, "there will be a way for the remaining processes to proceed to
completion in some sequence (not necessarily all simultaneously). In other words, some process
will be able to take all the resources it is requesting, after which it will eventually finish,
returning all the resources it holds and thus enabling another process to proceed." The 1984
column says this sequential version is the problem of Leung and Lai; the September 1983 column
had stated the simultaneous version `Σ_{p ∉ P'} (r_j(p) + a_j(p)) ≤ B_j`.

Formally, the remaining processes are run in the order of a list `L` without repetitions that
contains exactly the processes outside `P'`, and `L` is a reduction sequence
(`Cslib.Algorithms.Concurrency.DeadlockDetection.State.Reduces`) of the state with allocations
`r` and requests `a`, starting from the free amounts `B_j - Σ_{q ∉ P'} r_j(q)`: each process in
turn gets its request, finishes, and releases its allocation. `WellFormed` also asks that the
current allocations fit in the resources (`Σ_{p ∈ P} r_j(p) ≤ B_j`), which every actual system
state satisfies and which makes the free amounts natural numbers.

Resources are indexed `0, …, m - 1`, with `m` the length of the bound list; each process is a
triple `(c(p), r(p), a(p))` whose vectors have length `m`; processes are indexed by their
position in the process list. Numbers use the canonical binary encoding; the problem is
NP-complete in the strong sense (Leung and Lai, transformation from 3-PARTITION).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DEADLOCK RECOVERY is NP-complete.** Source: Johnson (1983, 1984), NP-completeness column;
Leung and Lai (1979). -/
public theorem_wanted deadlockRecovery_npComplete :
    deadlockRecoveryDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L deadlockRecoveryDec

end MetaMathlibExt.Complexity.NPComplete.DeadlockRecovery
