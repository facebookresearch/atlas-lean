/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSAFE LOCKING POLICY: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiversionSerializabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicy

open MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability
  (Schedule standard finalValue serial)

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

end MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicy
