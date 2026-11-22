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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiversionSerializabilityWanted

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

/-- A step `(c, x)`: `lock(x)` for `c = 0`, `update(x)` for `c = 1`, `unlock(x)` for `c = 2`. -/
abbrev Step := ℕ × ℕ

/-- An instance: the transactions `T₀, ..., Tₙ₋₁`, each a list of steps. -/
abbrev UnsafeLockingPolicyInstance := List (List Step)

/-- A transaction is well-formed: every step is a lock, update or unlock; for each variable `x`
it occurring in, it has at most one `lock(x)` and as many `unlock(x)`'s as `lock(x)`'s, the
`lock(x)` before the `unlock(x)`; and every `update(x)` lies strictly between them. -/
def TxnWellFormed (T : List Step) : Prop :=
  (∀ s ∈ T, s.1 < 3) ∧
    (∀ s ∈ T, T.count (0, s.2) ≤ 1 ∧ T.count (2, s.2) = T.count (0, s.2)) ∧
    (∀ s ∈ T, s.1 = 0 → T.idxOf s < T.idxOf (2, s.2)) ∧
    ∀ p : Fin T.length, T[p].1 = 1 →
      T.idxOf (0, T[p].2) < p ∧ (p : ℕ) < T.idxOf (2, T[p].2)

/-- Well-formedness of an instance: every transaction is well-formed. -/
def WellFormed (i : UnsafeLockingPolicyInstance) : Prop :=
  ∀ T ∈ i, TxnWellFormed T

/-- `σ` is a schedule of the transactions: transaction `t` occurs in `σ` exactly as often as
`Tₜ` has steps, and no other index occurs. -/
def IsSchedule (i : UnsafeLockingPolicyInstance) (σ : List ℕ) : Prop :=
  σ.Perm ((List.range i.length).flatMap fun t => List.replicate (i.getD t []).length t)

/-- The step at position `p` of the schedule `σ`, with its transaction: the `k`-th occurrence
of `t` executes the `k`-th step of `Tₜ`. -/
def stepAt (i : UnsafeLockingPolicyInstance) (σ : List ℕ) (p : ℕ) : ℕ × Step :=
  (σ.getD p 0, (i.getD (σ.getD p 0) []).getD ((σ.take p).count (σ.getD p 0)) (0, 0))

/-- `σ` is legal: between any two occurrences of `lock(x)` there is an occurrence of
`unlock(x)`. -/
def IsLegal (i : UnsafeLockingPolicyInstance) (σ : List ℕ) : Prop :=
  ∀ p < σ.length, ∀ q < σ.length, p < q → (stepAt i σ p).2.1 = 0 →
    (stepAt i σ q).2 = (stepAt i σ p).2 →
      ∃ r < q, p < r ∧ (stepAt i σ r).2 = (2, (stepAt i σ p).2.2)

/-- The schedule of reads and writes of `σ`: each `update(x)` of `Tₜ` becomes `read(x)`
followed by `write(x)` of `Tₜ`; locks and unlocks are dropped. -/
def readWriteSchedule (i : UnsafeLockingPolicyInstance) (σ : List ℕ) : Schedule :=
  (List.range σ.length).flatMap fun p =>
    let a := stepAt i σ p
    if a.2.1 = 1 then [(a.1, a.2.2, false), (a.1, a.2.2, true)] else []

/-- A read-write schedule of `n` transactions is serializable: some serial schedule of the
transactions, in the order of a permutation `π`, yields the same final value of every
variable. -/
def IsSerializable (n : ℕ) (S : Schedule) : Prop :=
  ∃ π : List ℕ, π.Perm (List.range n) ∧
    ∀ x : ℕ, finalValue S (standard S) x = finalValue (serial S π) (standard (serial S π)) x

/-- Some legal schedule of the transactions is not serializable. -/
def UnsafeLockingPolicyFeasible (i : UnsafeLockingPolicyInstance) : Prop :=
  ∃ σ : List ℕ, IsSchedule i σ ∧ IsLegal i σ ∧ ¬ IsSerializable i.length (readWriteSchedule i σ)

open Classical in
/-- UNSAFE LOCKING POLICY as a decision problem over bitstrings. -/
noncomputable def unsafeLockingPolicyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnsafeLockingPolicyInstance) x with
  | some i => decide (WellFormed i ∧ UnsafeLockingPolicyFeasible i)
  | none => false

/-- **UNSAFE LOCKING POLICY is NP-complete.** Source: Johnson (1983), problem [6];
Papadimitriou (1983); Yannakakis (1982). -/
public theorem_wanted unsafeLockingPolicy_npComplete :
    unsafeLockingPolicyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unsafeLockingPolicyDec

end MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicy
