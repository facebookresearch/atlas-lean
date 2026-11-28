/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSAFE LOCKING POLICY is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300,
doi:10.1016/0196-6774(83)90028-7, problem [6] UNSAFE LOCKING POLICY (reference: Papadimitriou
and Yannakakis; transformation from 3SAT), and Section 3 (serializability);
C. H. Papadimitriou, "Concurrency control by locking", SIAM J. Comput. 12 (1983), 215-226,
doi:10.1137/0212013;
M. Yannakakis, "A theory of safe locking policies in database systems", J. ACM 29 (1982),
718-740, doi:10.1145/322326.322333.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnsafeLockingPolicyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicy

open MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability
  (Schedule standard finalValue serial)

/-!
# UNSAFE LOCKING POLICY is NP-complete

INSTANCE: a set `X = {x₁, ..., xₘ}` of variables and a set `T₁, ..., Tₙ` of transactions, each
consisting of a sequence of steps of the form `lock(x)`, `update(x)` and `unlock(x)`, where each
`update(x)` occurs between a `lock(x)`-`unlock(x)` pair (although not necessarily contiguous to
either), and no transaction contains more than one `lock(x)`-`unlock(x)` pair for any `x ∈ X`.
QUESTION: is there a "legal" schedule for the transactions that is not serializable, i.e., is
there a non-serializable schedule `S` such that between any two occurrences of `lock(x)` in `S`
(for any `x ∈ X`), there is an occurrence of `unlock(x)`?

A schedule interleaves the transactions, keeping the steps of each transaction in order; it is
given by the sequence of transaction indices, the `k`-th occurrence of `t` executing the `k`-th
step of `Tₜ`. Serializability is the column's (Section 3): `S` is serializable if some serial
schedule, running the transactions one after another in the order of a permutation, yields the
same final values, "assuming that the result of each write depends on the values of all
variables that have previously been read by the transaction containing the write, and no matter
how it depends on those values". Locks and unlocks do not touch values, and `update(x)` is an
indivisible read of `x` followed by a write of `x`. The values are therefore computed by the
symbolic (Herbrand) semantics of
`WantedExt.Complexity.NPComplete.MultiversionSerializabilityWanted` (the same column's problem
[5]), reused here, on the schedule of reads and writes in which each `update(x)` of `Tₜ` becomes
`read(x)` immediately followed by `write(x)`, both of `Tₜ`: the written value is an uninterpreted
function of all values `Tₜ` has read so far, the current value of `x` included. Serial schedules
of the transactions are the serial schedules (`serial`) of this read-write schedule.

Variables are natural numbers. A step is a pair `(c, x)`: `c = 0` is `lock(x)`, `c = 1` is
`update(x)` and `c = 2` is `unlock(x)`; transaction `t` is the `t`-th list of steps.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNSAFE LOCKING POLICY is NP-complete.** Source: Johnson (1983), problem [6];
Papadimitriou (1983); Yannakakis (1982). -/
public theorem_wanted unsafeLockingPolicy_npComplete :
    unsafeLockingPolicyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unsafeLockingPolicyDec

end MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicy
