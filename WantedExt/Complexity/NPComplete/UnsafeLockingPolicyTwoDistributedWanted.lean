/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSAFE LOCKING POLICY for two distributed transactions is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300,
doi:10.1016/0196-6774(83)90028-7, Section 3, the distributed model preceding problem [8] and the
remark that UNSAFE LOCKING POLICY (problem [6]), restricted to total-order schedules, "becomes
NP-complete if an arbitrary number of sites is allowed in each transaction" for two transactions;
P. C. Kanellakis and C. H. Papadimitriou, "Is distributed locking harder?", J. Comput. System
Sci. 28 (1984), 103-120, doi:10.1016/0022-0000(84)90078-3 (conference version: Proc. 1st ACM
SIGACT-SIGMOD Symp. on Principles of Database Systems (1982), 98-107,
doi:10.1145/588111.588129).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnsafeLockingPolicyTwoDistributedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicyTwoDistributed

open MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability (Schedule)
open MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicy (Step TxnWellFormed IsSerializable)

/-!
# UNSAFE LOCKING POLICY for two distributed transactions is NP-complete

INSTANCE: a set of variables partitioned into sites, and two transactions `T₀`, `T₁`, each a
partially ordered set of steps `lock(x)`, `update(x)`, `unlock(x)` in which the steps involving
variables of any one site are totally ordered, and which, read in that order, satisfies the
conditions of UNSAFE LOCKING POLICY (each `update(x)` between a `lock(x)`-`unlock(x)` pair, at
most one such pair per variable). Any number of sites may be involved in each transaction.
QUESTION: is there a legal schedule that is a total order of all the steps, consistent with the
partial orders of both transactions, and that is not serializable?

This is the distributed model of Johnson's column (Section 3, before problem [8]): a transaction
is a partial order on its steps, totally ordered on the steps of each site; the result for two
transactions with an arbitrary number of sites, restricted to schedules that are total orders, is
due to Kanellakis and Papadimitriou. Legality ("between any two occurrences of `lock(x)` there is
an occurrence of `unlock(x)`") and the step format are those of
`WantedExt.Complexity.NPComplete.UnsafeLockingPolicyWanted` (problem [6]), and so is
serializability: the schedule's reads and writes (each `update(x)` is `read(x)` followed by
`write(x)`) leave, under the symbolic semantics reused there, the same final values as running
the two transactions one after the other in some order. A serial schedule of the distributed
model runs the transactions in the same order at every site. Since every update reads its
variable before writing it, the final value of a variable records which transactions updated it
in which order; so a total-order schedule leaves the final values of some serial schedule exactly
when it leaves those of the serial schedule that keeps each transaction's steps in their order in
the schedule, which is the one `IsSerializable` compares with.

Variables are natural numbers; the site of `x` is the `x`-th entry of a list of sites. A
transaction is its list of steps (in the format of the reused module), listed in some order
compatible with its partial order, together with the list of all pairs `(p, q)` such that step
`p` precedes step `q`: a strict order (`p < q`, transitively closed) that relates every two steps
on variables of the same site. A schedule lists the pairs `(t, p)`, step `p` of transaction `Tₜ`,
each exactly once, with `(t, p)` before `(t, q)` whenever `p` precedes `q` in `Tₜ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNSAFE LOCKING POLICY for two distributed transactions is NP-complete.** Source: Johnson
(1983), Section 3; Kanellakis and Papadimitriou (1984). -/
public theorem_wanted unsafeLockingPolicyTwoDistributed_npComplete :
    unsafeLockingPolicyTwoDistributedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unsafeLockingPolicyTwoDistributedDec

end MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicyTwoDistributed
