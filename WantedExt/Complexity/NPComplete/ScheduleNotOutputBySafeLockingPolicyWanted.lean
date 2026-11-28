/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULE NOT OUTPUT BY ANY SAFE LOCKING POLICY is NP-complete

Source:
M. Yannakakis, "Serializability by locking", J. ACM 31(2) (1984), 227-244,
doi:10.1145/62.322425 (Section 2: the model; Section 5: locking policies, Corollaries 2 and 3,
Theorem 6 and Corollary 4: "It is NP-complete to test whether a schedule cannot be produced by any
SSR-safe locking policy");
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300,
doi:10.1016/0196-6774(83)90028-7, comments to problem [6] UNSAFE LOCKING POLICY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ScheduleNotOutputBySafeLockingPolicyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ScheduleNotOutputBySafeLockingPolicy

open MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability
  (Schedule MultiversionSerializabilityInstance)
open MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicy (IsSerializable)

/-!
# SCHEDULE NOT OUTPUT BY ANY SAFE LOCKING POLICY is NP-complete

INSTANCE: a schedule `S` of a set `{T₁, ..., Tₙ}` of transactions without locks, whose steps
read or write single entities.
QUESTION: is `S` produced by no SSR-safe locking policy, i.e., is there no locking policy that
allows only state-serializable schedules and has a legal schedule whose steps without the locking
steps are `S`?

Yannakakis (Section 2): "A transaction is a finite sequence of steps. Each step reads some entity
`x` (denoted `rx`) or writes `x` (`wx`). The value written by a transaction in a write step is an
uninterpreted function of the values read thus far. We assume for simplicity that a transaction
does not write an entity more than once and does not read an entity after it has written it." A
schedule is state serializable (SSR) if some serial schedule of the transactions "for every
initial state of the database and interpretation of the functions computed by the transactions,
produces the same final state". Section 5: "a locking policy uses a set `LV` of locking variables
(not necessarily related to the entities) that can be locked in certain modes ... There is a
compatibility relation among the various modes that describes whether two different transactions
can simultaneously hold locks on a common variable. ... A locked transaction is a sequence of
action steps (read and write), locking steps ... and unlocking steps ..., put together in a
well-formed manner; that is, no variable is unlocked in mode `m` unless it is actually locked in
this mode, every variable is eventually unlocked in every mode in which it is locked, etc. A legal
schedule `S` of a set of locked transactions is a schedule that observes the compatibility
relation. A locking policy `P` is a mapping from the set of all transactions on the set of
entities `E` to the power set of locked transactions such that for each transaction `T` and each
`T̃ ∈ P(T)`, `T` and `T̃` have the same action steps in the same order." "A locking policy `P`
ensures criterion `A`, (or is `A`-safe) if for every set `{T₁, ..., Tₖ}` of transactions on `E`
with `P(Tᵢ) ≠ ∅`, and every `T̃ᵢ ∈ P(Tᵢ)`, any legal schedule of `{T̃₁, ..., T̃ₖ}` (without the
locks) satisfies `A`." Corollary 4 is the NP-completeness of the question above.

Johnson's column (comments to [6]) states the positive form: "given `S`, testing whether there
exists an `L` such that `S ∈ S_L` is NP-complete". By Yannakakis (Corollaries 2 and 3 with
Theorem 2) a schedule is produced by some SSR-safe locking policy exactly when all its
subschedules (the subsequences of the steps of a subset of the transactions) are live conflict
serializable, a polynomial-time check per subschedule, so the positive form is in coNP, and
Theorem 6 makes it coNP-complete; the NP-complete question is its complement, formalized here.
Membership in NP: a subset of the transactions whose subschedule is not live conflict
serializable is a certificate. Hardness: Theorem 6, by a reduction from satisfiability.

Representation. The instance is that of
`WantedExt.Complexity.NPComplete.MultiversionSerializabilityWanted`: the number `n` of
transactions and the schedule `S`, a list of actions `(t, x, w)`, transaction `t` reading
(`w = false`) or writing (`w = true`) entity `x`; transaction `t` is its actions in schedule order
(`txn`). As `{T₁, ..., Tₙ}` is a set of transactions obeying the assumptions above, the
transactions must be pairwise distinct and each must write no entity more than once and touch no
entity after writing it (`TxnOK`). State serializability is
`UnsafeLockingPolicy.IsSerializable`: some serial schedule leaves the same final symbolic
(Herbrand) values. A locked transaction is a list of `LockedStep`s over a type `LV` of locking
variables and a type `M` of modes; it holds variable `v` in mode `m` after its first `k` steps if
it has locked `v` in mode `m` and not unlocked it since (`HoldsAt`). Well-formedness
(`LockedWF`) reads the source's clauses as: every unlocking of `v` in mode `m` happens while `v`
is held in `m`, no locking of `v` in mode `m` happens while it is held in `m`, and nothing is held
at the end. A schedule of locked transactions interleaves them (the `k`-th occurrence of `t`
executes the `k`-th step of transaction `t`) and is legal if at no time two different
transactions hold a common variable in modes that are not compatible (`IsLegal`); `deleteLocks`
keeps its action steps. Sets of transactions are lists without repetition.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SCHEDULE NOT OUTPUT BY ANY SAFE LOCKING POLICY is NP-complete.** Source: Yannakakis (1984),
Corollary 4 and Theorem 6; Johnson (1983), comments to [6]. -/
public theorem_wanted scheduleNotOutputBySafeLockingPolicy_npComplete :
    scheduleNotOutputBySafeLockingPolicyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L scheduleNotOutputBySafeLockingPolicyDec

end MetaMathlibExt.Complexity.NPComplete.ScheduleNotOutputBySafeLockingPolicy
