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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnsafeLockingPolicyWanted

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

/-- A distributed transaction: its steps, and the pairs `(p, q)` of step positions such that
step `p` precedes step `q`. -/
abbrev DistTxn := List Step × List (ℕ × ℕ)

/-- An instance: the sites of the variables (`x` resides at the `x`-th entry), and the
transactions `T₀`, `T₁`. -/
abbrev UnsafeLockingPolicyTwoDistributedInstance := List ℕ × DistTxn × DistTxn

/-- The site of the variable of a step. -/
def siteOf (sites : List ℕ) (s : Step) : ℕ := sites.getD s.2 0

/-- A distributed transaction is well-formed: its step list is a well-formed transaction of
UNSAFE LOCKING POLICY; every variable has a site; the precedence pairs are strict, forward in the
step list and transitively closed; and every two steps on variables of the same site are
related. -/
def DistTxnWellFormed (sites : List ℕ) (T : DistTxn) : Prop :=
  TxnWellFormed T.1 ∧ (∀ s ∈ T.1, s.2 < sites.length) ∧
    (∀ a ∈ T.2, a.1 < a.2 ∧ a.2 < T.1.length) ∧
    (∀ a ∈ T.2, ∀ b ∈ T.2, a.2 = b.1 → (a.1, b.2) ∈ T.2) ∧
    ∀ p q : Fin T.1.length, p < q → siteOf sites T.1[p] = siteOf sites T.1[q] →
      ((p : ℕ), (q : ℕ)) ∈ T.2

/-- Well-formedness of an instance: both transactions are well-formed. -/
def WellFormed (i : UnsafeLockingPolicyTwoDistributedInstance) : Prop :=
  DistTxnWellFormed i.1 i.2.1 ∧ DistTxnWellFormed i.1 i.2.2

/-- Transaction `t` (`T₀` for `t = 0`, `T₁` otherwise). -/
def txn (i : UnsafeLockingPolicyTwoDistributedInstance) (t : ℕ) : DistTxn :=
  if t = 0 then i.2.1 else i.2.2

/-- `σ` is a schedule: it lists every step `(t, p)` of both transactions exactly once, and
`(t, p)` occurs before `(t, q)` whenever `p` precedes `q` in `Tₜ`. -/
def IsSchedule (i : UnsafeLockingPolicyTwoDistributedInstance) (σ : List (ℕ × ℕ)) : Prop :=
  σ.Perm ((List.range i.2.1.1.length).map (fun p => (0, p)) ++
      (List.range i.2.2.1.length).map (fun p => (1, p))) ∧
    ∀ t < 2, ∀ a ∈ (txn i t).2, σ.idxOf (t, a.1) < σ.idxOf (t, a.2)

/-- The step at position `r` of the schedule `σ`. -/
def stepAt (i : UnsafeLockingPolicyTwoDistributedInstance) (σ : List (ℕ × ℕ)) (r : ℕ) : Step :=
  (txn i (σ.getD r (0, 0)).1).1.getD (σ.getD r (0, 0)).2 (0, 0)

/-- `σ` is legal: between any two occurrences of `lock(x)` there is an occurrence of
`unlock(x)`. -/
def IsLegal (i : UnsafeLockingPolicyTwoDistributedInstance) (σ : List (ℕ × ℕ)) : Prop :=
  ∀ p < σ.length, ∀ q < σ.length, p < q → (stepAt i σ p).1 = 0 →
    stepAt i σ q = stepAt i σ p → ∃ r < q, p < r ∧ stepAt i σ r = (2, (stepAt i σ p).2)

/-- The schedule of reads and writes of `σ`: each `update(x)` of `Tₜ` becomes `read(x)`
followed by `write(x)` of `Tₜ`; locks and unlocks are dropped. -/
def readWriteSchedule (i : UnsafeLockingPolicyTwoDistributedInstance) (σ : List (ℕ × ℕ)) :
    Schedule :=
  (List.range σ.length).flatMap fun r =>
    let s := stepAt i σ r
    if s.1 = 1 then [((σ.getD r (0, 0)).1, s.2, false), ((σ.getD r (0, 0)).1, s.2, true)]
    else []

/-- Some legal schedule of the two transactions is not serializable. -/
def UnsafeLockingPolicyTwoDistributedFeasible
    (i : UnsafeLockingPolicyTwoDistributedInstance) : Prop :=
  ∃ σ : List (ℕ × ℕ), IsSchedule i σ ∧ IsLegal i σ ∧ ¬ IsSerializable 2 (readWriteSchedule i σ)

open Classical in
/-- UNSAFE LOCKING POLICY for two distributed transactions as a decision problem over
bitstrings. -/
noncomputable def unsafeLockingPolicyTwoDistributedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnsafeLockingPolicyTwoDistributedInstance) x with
  | some i => decide (WellFormed i ∧ UnsafeLockingPolicyTwoDistributedFeasible i)
  | none => false

/-- **UNSAFE LOCKING POLICY for two distributed transactions is NP-complete.** Source: Johnson
(1983), Section 3; Kanellakis and Papadimitriou (1984). -/
public theorem_wanted unsafeLockingPolicyTwoDistributed_npComplete :
    unsafeLockingPolicyTwoDistributedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unsafeLockingPolicyTwoDistributedDec

end MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicyTwoDistributed
