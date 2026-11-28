/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULE NOT OUTPUT BY ANY SAFE LOCKING POLICY: definitions

Source:
M. Yannakakis, "Serializability by locking", J. ACM 31(2) (1984), 227-244,
doi:10.1145/62.322425 (Section 2: the model; Section 5: locking policies, Corollaries 2 and 3,
Theorem 6 and Corollary 4: "It is NP-complete to test whether a schedule cannot be produced by any
SSR-safe locking policy");
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300,
doi:10.1016/0196-6774(83)90028-7, comments to problem [6] UNSAFE LOCKING POLICY.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnsafeLockingPolicyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ScheduleNotOutputBySafeLockingPolicy

open MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability
  (Schedule MultiversionSerializabilityInstance)
open MetaMathlibExt.Complexity.NPComplete.UnsafeLockingPolicy (IsSerializable)

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

end MetaMathlibExt.Complexity.NPComplete.ScheduleNotOutputBySafeLockingPolicy
