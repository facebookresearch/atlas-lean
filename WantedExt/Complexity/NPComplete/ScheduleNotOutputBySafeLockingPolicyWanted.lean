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
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnsafeLockingPolicyWanted

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

/-- An action step `(x, w)`: a read (`w = false`) or a write (`w = true`) of entity `x`. -/
abbrev Act := ℕ × Bool

/-- Transaction `t` of the schedule `S`: its actions in schedule order. -/
def txn (S : Schedule) (t : ℕ) : List Act :=
  (S.filter fun a => a.1 == t).map fun a => (a.2.1, a.2.2)

/-- A transaction obeys the model's assumptions: after writing an entity it neither reads nor
writes that entity again. -/
def TxnOK (T : List Act) : Prop :=
  ∀ i j : Fin T.length, i < j → T[i].2 = true → T[j].1 ≠ T[i].1

/-- A step of a locked transaction: an action step, or the locking or unlocking of a locking
variable in a mode. -/
inductive LockedStep (LV M : Type) where
  | act (a : Act)
  | lock (v : LV) (m : M)
  | unlock (v : LV) (m : M)

variable {LV M : Type}

/-- The action steps of a locked transaction, in order. -/
def actions (L : List (LockedStep LV M)) : List Act :=
  L.filterMap fun s => match s with
    | .act a => some a
    | _ => none

/-- After its first `k` steps the locked transaction `L` holds `v` in mode `m`: one of these steps
locks `v` in mode `m` and no later one of them unlocks `v` in mode `m`. -/
def HoldsAt (L : List (LockedStep LV M)) (k : ℕ) (v : LV) (m : M) : Prop :=
  ∃ i < k, L[i]? = some (.lock v m) ∧ ∀ l, i < l → l < k → L[l]? ≠ some (.unlock v m)

/-- A locked transaction is well formed: it unlocks `v` in mode `m` only while holding `v` in
mode `m`, locks `v` in mode `m` only while not holding it in mode `m`, and holds nothing at the
end. -/
def LockedWF (L : List (LockedStep LV M)) : Prop :=
  (∀ j v m, L[j]? = some (.unlock v m) → HoldsAt L j v m) ∧
    (∀ j v m, L[j]? = some (.lock v m) → ¬ HoldsAt L j v m) ∧
    ∀ v m, ¬ HoldsAt L L.length v m

/-- `P` is a locking policy: every locked transaction in `P T` is well formed and has the action
steps of `T` in the same order. -/
def IsLockingPolicy (P : List Act → Set (List (LockedStep LV M))) : Prop :=
  ∀ T, ∀ L ∈ P T, actions L = T ∧ LockedWF L

/-- `σ` interleaves transactions of lengths `lens`: transaction `t` occurs in `σ` exactly
`lens[t]` times, and no other index occurs. -/
def IsInterleaving (lens : List ℕ) (σ : List ℕ) : Prop :=
  σ.Perm ((List.range lens.length).flatMap fun t => List.replicate (lens.getD t 0) t)

/-- `σ` is a legal schedule of the locked transactions `Ls`: it interleaves them, and at no time
do two different transactions hold a common variable in modes that are not compatible. -/
def IsLegal (compat : M → M → Prop) (Ls : List (List (LockedStep LV M))) (σ : List ℕ) : Prop :=
  IsInterleaving (Ls.map List.length) σ ∧
    ∀ p ≤ σ.length, ∀ t t', t ≠ t' → ∀ v m m',
      HoldsAt (Ls.getD t []) ((σ.take p).count t) v m →
        HoldsAt (Ls.getD t' []) ((σ.take p).count t') v m' → compat m m'

/-- The schedule of action steps of the schedule `σ` of locked transactions `Ls`, without the
locking and unlocking steps: the `k`-th occurrence of `t` in `σ` executes the `k`-th step of
transaction `t`. -/
def deleteLocks (Ls : List (List (LockedStep LV M))) (σ : List ℕ) : Schedule :=
  (List.range σ.length).filterMap fun p =>
    match (Ls.getD (σ.getD p 0) [])[(σ.take p).count (σ.getD p 0)]? with
    | some (.act a) => some (σ.getD p 0, a.1, a.2)
    | _ => none

/-- `P` is SSR-safe: for every set of transactions `T₀, ..., Tₖ₋₁` (pairwise distinct, obeying
the model's assumptions) and every choice of `Lⱼ ∈ P Tⱼ`, every legal schedule of
`L₀, ..., Lₖ₋₁` without the locks is state serializable. -/
def IsSSRSafe (compat : M → M → Prop) (P : List Act → Set (List (LockedStep LV M))) : Prop :=
  ∀ Ts : List (List Act), Ts.Nodup → (∀ T ∈ Ts, TxnOK T) →
    ∀ Ls : List (List (LockedStep LV M)), Ls.length = Ts.length →
      (∀ j < Ts.length, Ls.getD j [] ∈ P (Ts.getD j [])) →
        ∀ σ, IsLegal compat Ls σ → IsSerializable Ts.length (deleteLocks Ls σ)

/-- `P` produces the schedule `S` of the `n` transactions: for some choice of
`Lₜ ∈ P (txn S t)`, `t < n`, some legal schedule of `L₀, ..., Lₙ₋₁` without the locks is `S`. -/
def Produces (compat : M → M → Prop) (P : List Act → Set (List (LockedStep LV M)))
    (n : ℕ) (S : Schedule) : Prop :=
  ∃ Ls : List (List (LockedStep LV M)), Ls.length = n ∧
    (∀ t < n, Ls.getD t [] ∈ P (txn S t)) ∧ ∃ σ, IsLegal compat Ls σ ∧ deleteLocks Ls σ = S

/-- Well-formedness of an instance: every action belongs to one of the transactions
`0, ..., n - 1`, these transactions are pairwise distinct, and each obeys the model's
assumptions. -/
def WellFormed (i : MultiversionSerializabilityInstance) : Prop :=
  (∀ a ∈ i.2, a.1 < i.1) ∧ ((List.range i.1).map (txn i.2)).Nodup ∧
    ∀ t < i.1, TxnOK (txn i.2 t)

/-- No SSR-safe locking policy produces the schedule: for all types of locking variables and of
modes, every compatibility relation and every locking policy that produces the schedule, the
policy is not SSR-safe. -/
def ScheduleNotOutputBySafeLockingPolicyFeasible (i : MultiversionSerializabilityInstance) :
    Prop :=
  ∀ (LV M : Type) (compat : M → M → Prop) (P : List Act → Set (List (LockedStep LV M))),
    IsLockingPolicy P → Produces compat P i.1 i.2 → ¬ IsSSRSafe compat P

open Classical in
/-- SCHEDULE NOT OUTPUT BY ANY SAFE LOCKING POLICY as a decision problem over bitstrings. -/
noncomputable def scheduleNotOutputBySafeLockingPolicyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiversionSerializabilityInstance) x with
  | some i => decide (WellFormed i ∧ ScheduleNotOutputBySafeLockingPolicyFeasible i)
  | none => false

/-- **SCHEDULE NOT OUTPUT BY ANY SAFE LOCKING POLICY is NP-complete.** Source: Yannakakis (1984),
Corollary 4 and Theorem 6; Johnson (1983), comments to [6]. -/
public theorem_wanted scheduleNotOutputBySafeLockingPolicy_npComplete :
    scheduleNotOutputBySafeLockingPolicyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L scheduleNotOutputBySafeLockingPolicyDec

end MetaMathlibExt.Complexity.NPComplete.ScheduleNotOutputBySafeLockingPolicy
