/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.Serializability

/-!
# Two-phase locking

A locked schedule is a list of actions `Action n X`: the reads and writes of the transactions
(`Op n X`), together with lock requests `lock t x m` (shared or exclusive mode) and releases
`unlock t x`. Positions in the list are points in time, and `HoldsBefore s t x m p` says that just
before position `p`, transaction `t` holds a lock on `x` whose mode covers `m` (an exclusive lock
covers both modes).

* `LocksCover s`: every read is covered by a shared or exclusive lock of its transaction, and every
  write by an exclusive lock. `WellFormed s` adds `ReleasesLocks s`: every lock is eventually
  released, so that transactions end holding no locks.
* `Legal s`: two transactions never hold locks on the same item at the same time unless both locks
  are shared.
* `TwoPhase s`: every lock request of a transaction precedes every release of that transaction (a
  growing phase followed by a shrinking phase).
* `StrictTwoPhase s`: two-phase, and a transaction releases its exclusive locks only after its last
  read or write (the model has no commit or abort actions; the last read or write stands in for
  the end of the transaction).
All of these are decidable for concrete schedules.

`ops s` is the schedule of reads and writes obtained by erasing the lock actions.

`TwoPhase.conflictSerializable` is the **two-phase locking theorem**: if the reads and writes of
`s` are distinct (`(ops s).Nodup`), and `s` is covered by locks, legal and two-phase, then `ops s`
is conflict-serializable (in particular this holds for well-formed schedules). The proof ranks
each transaction by the position of its first release (a bound on its lock point): along every
edge `i → j` of the precedence graph, `i` must release the item before `j` acquires a conflicting
lock on it, and `j` acquires all its locks before releasing any, so the rank strictly increases
and the precedence graph is acyclic. `StrictTwoPhase.conflictSerializable`: under the same
hypotheses every strict 2PL schedule is conflict-serializable.

## References

* P. A. Bernstein, V. Hadzilacos and N. Goodman, *Concurrency Control and Recovery in Database
  Systems*, Addison-Wesley, 1987, Chapter 3 (two-phase locking and the 2PL theorem).
* K. P. Eswaran, J. N. Gray, R. A. Lorie and I. L. Traiger, *The notions of consistency and
  predicate locks in a database system*, Communications of the ACM 19(11), 1976.
-/

@[expose] public section

namespace Cslib.Databases

open scoped List

/-- **Lock mode.** A lock is held in one of two modes: shared (a read lock) or exclusive (a write
lock). -/
inductive LockMode
  /-- A shared (read) lock. -/
  | shared
  /-- An exclusive (write) lock. -/
  | exclusive
deriving DecidableEq

instance (P : LockMode → Prop) [DecidablePred P] : Decidable (∃ m, P m) :=
  decidable_of_iff (P .shared ∨ P .exclusive)
    ⟨fun h => h.elim (⟨_, ·⟩) (⟨_, ·⟩), fun ⟨m, hm⟩ => by cases m; exacts [Or.inl hm, Or.inr hm]⟩

instance (P : LockMode → Prop) [DecidablePred P] : Decidable (∀ m, P m) :=
  decidable_of_iff (P .shared ∧ P .exclusive)
    ⟨fun h m => by cases m; exacts [h.1, h.2], fun h => ⟨h _, h _⟩⟩

/-- **Lock mode coverage.** A lock mode $m'$ covers a lock mode $m$ when a lock in mode $m'$
permits what a lock in mode $m$ permits: an exclusive lock covers both modes, and a shared lock
covers only the shared mode. -/
def LockMode.Covers : LockMode → LockMode → Prop
  | .exclusive, _ => True
  | .shared, m => m = .shared

instance : DecidableRel LockMode.Covers := fun m m' => by
  cases m <;> unfold LockMode.Covers <;> infer_instance

/-- The lock mode an access requires: shared for a read, exclusive for a write. -/
def Access.mode : Access → LockMode
  | .read => .shared
  | .write => .exclusive

variable {n : ℕ} {X : Type*}

/-- **Action of a locked schedule.** For $n$ transactions, numbered $0, \dots, n-1$, and a type $X$
of data items, an action of a locked schedule is one of three kinds: a read or write operation; a
lock request, in which a transaction $t$ acquires a lock on an item $x \in X$ in a lock mode $m$
(shared or exclusive); or a release, in which a transaction $t$ releases its lock on an item
$x \in X$. -/
inductive Action (n : ℕ) (X : Type*)
  /-- A read or a write. -/
  | op (o : Op n X)
  /-- Transaction `t` acquires a lock on `x` in mode `m`. -/
  | lock (t : Fin n) (x : X) (m : LockMode)
  /-- Transaction `t` releases its lock on `x`. -/
  | unlock (t : Fin n) (x : X)
deriving DecidableEq

/-- **Reads and writes of a locked schedule.** For a locked schedule $s$, the schedule of reads and
writes of $s$: its reads and writes in order, with the lock requests and releases erased. -/
def ops (s : List (Action n X)) : List (Op n X) :=
  s.filterMap fun
    | .op o => some o
    | _ => none

/-- **Holding a lock.** Let $s$ be a locked schedule, $t$ a transaction, $x$ a data item, $m$ a
lock mode and $p$ a natural number. Transaction $t$ holds a lock on $x$ covering mode $m$ just
before position $p$ of $s$ when there is a position $q < p$ at which $s$ has a lock request by $t$
on $x$ in some mode $m'$ that covers $m$, and for no position $r$ with $q < r < p$ is the action
of $s$ at $r$ a release of $x$ by $t$. -/
def HoldsBefore (s : List (Action n X)) (t : Fin n) (x : X) (m : LockMode) (p : ℕ) : Prop :=
  ∃ q < p, (∃ m', s[q]? = some (.lock t x m') ∧ m'.Covers m) ∧
    ∀ r < p, q < r → s[r]? ≠ some (.unlock t x)

instance [DecidableEq X] (s : List (Action n X)) (t : Fin n) (x : X) (m : LockMode) (p : ℕ) :
    Decidable (HoldsBefore s t x m p) := by
  unfold HoldsBefore
  infer_instance

/-- **Schedules covered by locks.** A locked schedule $s$ is covered by locks when every read or
write is protected by a lock of its transaction: whenever $s$ has at position $p$ a read or write
$o$ by transaction $t$ on item $x$, just before position $p$ transaction $t$ holds a lock on $x$
(acquired at an earlier position and not released since) whose mode covers the mode $o$ requires,
namely shared for a read and exclusive for a write; an exclusive lock covers both modes. -/
def LocksCover (s : List (Action n X)) : Prop :=
  ∀ p o, s[p]? = some (.op o) → HoldsBefore s o.txn o.item o.access.mode p

/-- **Schedules that release every lock.** A locked schedule $s$ releases its locks when every lock
request is followed by a matching release: whenever $s$ has at position $q$ a lock request (in
either mode) by transaction $t$ on item $x$, there is a position $r > q$ at which $s$ has a
release by $t$ of $x$.

In particular, transactions end holding no locks. -/
def ReleasesLocks (s : List (Action n X)) : Prop :=
  ∀ (q : ℕ) (t : Fin n) (x : X) (m : LockMode), s[q]? = some (.lock t x m) →
    ∃ r, q < r ∧ s[r]? = some (.unlock t x)

/-- **Well-formed locked schedules.** A locked schedule $s$ (a list of reads, writes, lock
requests and lock releases of transactions) is well formed when its accesses are covered by
locks and it releases its locks: every read or write in $s$ is preceded by a lock request of its
own transaction on its item, in a mode covering the access (shared or exclusive for a read,
exclusive for a write), with no release of that item by that transaction in between; and every
lock request in $s$ by a transaction on an item is followed later in $s$ by a release of that
item by the same transaction. -/
def WellFormed (s : List (Action n X)) : Prop := LocksCover s ∧ ReleasesLocks s

/-- **Lock compatibility at a point.** A locked schedule $s$ is legal just before position $p$
when, for every data item $x$, all distinct transactions $t \ne t'$ and all lock modes $m$, $m'$:
if $t$ holds a lock on $x$ covering $m$ and $t'$ holds a lock on $x$ covering $m'$ just before
position $p$ of $s$, then $m$ and $m'$ are both the shared mode. In words, two transactions do not
both hold locks on the same item unless both locks are shared. -/
def LegalAt (s : List (Action n X)) (p : ℕ) : Prop :=
  ∀ x t t' m m', t ≠ t' → HoldsBefore s t x m p → HoldsBefore s t' x m' p →
    m = .shared ∧ m' = .shared

/-- **Locked items.** The list of data items locked in a locked schedule $s$: for each lock request
of $s$, in order, the item it locks, so an item appears once for each lock request on it. -/
def lockedItems (s : List (Action n X)) : List X :=
  s.filterMap fun
    | .lock _ x _ => some x
    | _ => none

theorem HoldsBefore.mem_lockedItems {s : List (Action n X)} {t : Fin n} {x : X} {m : LockMode}
    {p : ℕ} (h : HoldsBefore s t x m p) : x ∈ lockedItems s := by
  obtain ⟨q, -, ⟨m', hq, -⟩, -⟩ := h
  exact List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hq, rfl⟩

theorem legalAt_iff (s : List (Action n X)) (p : ℕ) :
    LegalAt s p ↔ ∀ x ∈ lockedItems s, ∀ t t' m m', t ≠ t' → HoldsBefore s t x m p →
      HoldsBefore s t' x m' p → m = .shared ∧ m' = .shared :=
  ⟨fun h x _ => h x, fun h x t t' m m' htt' ht => h x ht.mem_lockedItems t t' m m' htt' ht⟩

instance [DecidableEq X] (s : List (Action n X)) (p : ℕ) : Decidable (LegalAt s p) :=
  decidable_of_iff _ (legalAt_iff s p).symm

/-- **Legal locked schedule.** A locked schedule $s$ of length $\ell$ is legal when it satisfies
lock compatibility at every point $p \le \ell$: just before position $p$, no two distinct
transactions both hold locks on the same item unless both locks are shared.

After the last action the locks no longer change, so the points $p \le \ell$ are all the points. -/
def Legal (s : List (Action n X)) : Prop := ∀ p ≤ s.length, LegalAt s p

instance [DecidableEq X] (s : List (Action n X)) : Decidable (Legal s) := by
  unfold Legal
  infer_instance

/-- **Two-phase schedules.** A locked schedule $s$ is two-phase when every lock request of a
transaction precedes every release of that transaction: whenever $s$ has at position $p$ a release
by transaction $t$ and at position $q$ a lock request by $t$ (on any items, in any mode), then
$q < p$. -/
def TwoPhase (s : List (Action n X)) : Prop :=
  ∀ (t : Fin n) (p q : ℕ) (x y : X) (m : LockMode),
    s[p]? = some (.unlock t x) → s[q]? = some (.lock t y m) → q < p

/-- **Strict two-phase schedules.** A locked schedule $s$ is strict two-phase when it is two-phase
and every transaction releases its exclusive locks only after its last read or write: whenever
$s$ has at position $p$ a release by transaction $t$ of item $x$ and just before position $p$
transaction $t$ holds an exclusive lock on $x$, every read or write of $t$ in $s$ occurs at a
position before $p$. -/
def StrictTwoPhase (s : List (Action n X)) : Prop :=
  TwoPhase s ∧ ∀ t x p, s[p]? = some (.unlock t x) → HoldsBefore s t x .exclusive p →
    ∀ q o, s[q]? = some (.op o) → o.txn = t → q < p

/-- **Lock coverage at a position.** For a locked schedule $s$ and a position $p$: if $s$ has at
position $p$ a read or write $o$ by transaction $t$ on item $x$, then just before position $p$
transaction $t$ holds a lock on $x$ whose mode covers the mode $o$ requires (shared for a read,
exclusive for a write; an exclusive lock covers both modes). If position $p$ holds a lock request
or a release, or lies beyond the end of $s$, the condition holds trivially. -/
def LocksCoverAt (s : List (Action n X)) (p : ℕ) : Prop :=
  match s[p]? with
  | some (.op o) => HoldsBefore s o.txn o.item o.access.mode p
  | _ => True

instance [DecidableEq X] (s : List (Action n X)) : DecidablePred (LocksCoverAt s) := fun p => by
  unfold LocksCoverAt
  cases s[p]? with
  | none => exact isTrue trivial
  | some a => cases a <;> first | exact isTrue trivial | (dsimp only; infer_instance)

theorem locksCover_iff (s : List (Action n X)) :
    LocksCover s ↔ ∀ p < s.length, LocksCoverAt s p := by
  constructor
  · intro h p _
    unfold LocksCoverAt
    split
    · next o ho => exact h p o ho
    · trivial
  · intro h p o ho
    have hp : p < s.length := (List.getElem?_eq_some_iff.mp ho).1
    have := h p hp
    unfold LocksCoverAt at this
    rw [ho] at this
    exact this

instance [DecidableEq X] (s : List (Action n X)) : Decidable (LocksCover s) :=
  decidable_of_iff _ (locksCover_iff s).symm

/-- **Release of the lock requested at a position.** For a locked schedule $s$ and a position $q$:
if $s$ has at position $q$ a lock request (in either mode) by transaction $t$ on item $x$, then
there is a position $r$ with $q < r$ and $r$ less than the length of $s$ at which $s$ has a release
by $t$ of $x$. If position $q$ holds a read, a write or a release, or lies beyond the end of $s$,
the condition holds trivially. -/
def ReleasedAt (s : List (Action n X)) (q : ℕ) : Prop :=
  match s[q]? with
  | some (.lock t x _) => ∃ r < s.length, q < r ∧ s[r]? = some (.unlock t x)
  | _ => True

instance [DecidableEq X] (s : List (Action n X)) : DecidablePred (ReleasedAt s) := fun q => by
  unfold ReleasedAt
  cases s[q]? with
  | none => exact isTrue trivial
  | some a => cases a <;> first | exact isTrue trivial | (dsimp only; infer_instance)

theorem releasesLocks_iff (s : List (Action n X)) :
    ReleasesLocks s ↔ ∀ q < s.length, ReleasedAt s q := by
  constructor
  · intro h q _
    unfold ReleasedAt
    split
    · rename_i t x m hq
      obtain ⟨r, hqr, hr⟩ := h q t x m hq
      exact ⟨r, (List.getElem?_eq_some_iff.mp hr).1, hqr, hr⟩
    · trivial
  · intro h q t x m hq
    have := h q (List.getElem?_eq_some_iff.mp hq).1
    unfold ReleasedAt at this
    rw [hq] at this
    obtain ⟨r, -, hqr, hr⟩ := this
    exact ⟨r, hqr, hr⟩

instance [DecidableEq X] (s : List (Action n X)) : Decidable (ReleasesLocks s) :=
  decidable_of_iff _ (releasesLocks_iff s).symm

instance [DecidableEq X] (s : List (Action n X)) : Decidable (WellFormed s) := by
  unfold WellFormed
  infer_instance

/-- **Two-phase condition at a pair of positions.** For a locked schedule $s$ and positions $p$ and
$q$: if $s$ has at position $p$ a release by transaction $t$ and at position $q$ a lock request by
the same transaction $t$, then $q < p$. For every other pair of positions, including positions
beyond the end of $s$, the condition holds trivially. -/
def TwoPhaseAt (s : List (Action n X)) (p q : ℕ) : Prop :=
  match s[p]?, s[q]? with
  | some (.unlock t _), some (.lock t' _ _) => t' = t → q < p
  | _, _ => True

instance (s : List (Action n X)) (p q : ℕ) : Decidable (TwoPhaseAt s p q) := by
  unfold TwoPhaseAt
  cases s[p]? with
  | none => exact isTrue trivial
  | some a =>
    cases s[q]? with
    | none => cases a <;> exact isTrue trivial
    | some b => cases a <;> cases b <;> first | exact isTrue trivial | (dsimp only; infer_instance)

theorem twoPhase_iff (s : List (Action n X)) :
    TwoPhase s ↔ ∀ p < s.length, ∀ q < s.length, TwoPhaseAt s p q := by
  constructor
  · intro h p _ q _
    unfold TwoPhaseAt
    split
    · rename_i t x t' y m hp hq
      intro htt
      exact h t p q x y m hp (htt ▸ hq)
    · trivial
  · intro h t p q x y m hp hq
    have := h p (List.getElem?_eq_some_iff.mp hp).1 q (List.getElem?_eq_some_iff.mp hq).1
    unfold TwoPhaseAt at this
    rw [hp, hq] at this
    exact this rfl

instance (s : List (Action n X)) : Decidable (TwoPhase s) :=
  decidable_of_iff _ (twoPhase_iff s).symm

/-- **Strictness at a pair of positions.** For a locked schedule $s$ and positions $p$ and $q$: if
$s$ has at position $p$ a release by transaction $t$ of item $x$, just before position $p$
transaction $t$ holds an exclusive lock on $x$, and $s$ has at position $q$ a read or write by
$t$, then $q < p$. For every other pair of positions, including positions beyond the end of $s$,
the condition holds trivially. -/
def StrictAt (s : List (Action n X)) (p q : ℕ) : Prop :=
  match s[p]?, s[q]? with
  | some (.unlock t x), some (.op o) => o.txn = t → HoldsBefore s t x .exclusive p → q < p
  | _, _ => True

instance [DecidableEq X] (s : List (Action n X)) (p q : ℕ) : Decidable (StrictAt s p q) := by
  unfold StrictAt
  cases s[p]? with
  | none => exact isTrue trivial
  | some a =>
    cases s[q]? with
    | none => cases a <;> exact isTrue trivial
    | some b => cases a <;> cases b <;> first | exact isTrue trivial | (dsimp only; infer_instance)

theorem strictTwoPhase_iff (s : List (Action n X)) :
    StrictTwoPhase s ↔ TwoPhase s ∧ ∀ p < s.length, ∀ q < s.length, StrictAt s p q := by
  refine and_congr Iff.rfl ⟨fun h p _ q _ => ?_, fun h t x p hp hx q o hq ho => ?_⟩
  · unfold StrictAt
    split
    · rename_i t x o hp hq
      exact fun ho hx => h t x p hp hx q o hq ho
    · trivial
  · have := h p (List.getElem?_eq_some_iff.mp hp).1 q (List.getElem?_eq_some_iff.mp hq).1
    unfold StrictAt at this
    rw [hp, hq] at this
    exact this ho hx

instance [DecidableEq X] (s : List (Action n X)) : Decidable (StrictTwoPhase s) :=
  decidable_of_iff _ (strictTwoPhase_iff s).symm

/-- **Release test.** For a transaction $t$, this Boolean test on the actions of a locked schedule
returns true exactly when the action is a release by $t$ of its lock on some item. -/
def Action.isUnlockBy (t : Fin n) : Action n X → Bool
  | .unlock t' _ => t' == t
  | _ => false

private theorem map_op_ops (s : List (Action n X)) :
    (ops s).map Action.op = s.filter fun a => match a with
      | .op _ => true
      | _ => false := by
  induction s with
  | nil => rfl
  | cons a s ih => cases a <;> simp [ops, ih] at *

private theorem exists_lt_of_pair_sublist_ops {s : List (Action n X)} {a b : Op n X}
    (h : [a, b] <+ ops s) : ∃ i j : ℕ, i < j ∧ s[i]? = some (.op a) ∧ s[j]? = some (.op b) := by
  have h' : [Action.op a, Action.op b] <+ s := by
    have := h.map Action.op
    rw [map_op_ops] at this
    exact this.trans List.filter_sublist
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp h'
  exact ⟨f 0, f 1, f.strictMono Nat.zero_lt_one, by simpa using (hf 0).symm,
    by simpa using (hf 1).symm⟩

private theorem findIdx_le_of_getElem? {α : Type*} {p : α → Bool} {l : List α} {r : ℕ} {c : α}
    (hr : l[r]? = some c) (hc : p c = true) : l.findIdx p ≤ r := by
  by_contra hlt
  obtain ⟨hrl, hrc⟩ := List.getElem?_eq_some_iff.mp hr
  have := List.not_of_lt_findIdx (Nat.lt_of_not_le hlt)
  simp [hrc, hc] at this

/-- In a two-phase schedule, every lock request of `t` comes before its first release. -/
private theorem lt_findIdx_of_lock {s : List (Action n X)} (h2 : TwoPhase s) {t : Fin n} {q : ℕ}
    {x : X} {m : LockMode} (hq : s[q]? = some (.lock t x m)) :
    q < s.findIdx (Action.isUnlockBy t) := by
  by_contra hle
  have hlen : s.findIdx (Action.isUnlockBy t) < s.length :=
    lt_of_le_of_lt (Nat.le_of_not_lt hle) (List.getElem?_eq_some_iff.mp hq).1
  have hu := List.findIdx_getElem (w := hlen)
  generalize hc : s[s.findIdx (Action.isUnlockBy t)] = c at hu
  cases c with
  | unlock t' y =>
    simp only [Action.isUnlockBy, beq_iff_eq] at hu
    subst hu
    have := h2 t' _ q y x m (by rw [List.getElem?_eq_some_iff]; exact ⟨hlen, hc⟩) hq
    omega
  | op => simp [Action.isUnlockBy] at hu
  | lock => simp [Action.isUnlockBy] at hu

private theorem conflict_mode {a b : Op n X} (h : a.Conflicts b) :
    a.access.mode = .exclusive ∨ b.access.mode = .exclusive := by
  rcases h.2.2 with h | h
  · exact Or.inl (by simp [h, Access.mode])
  · exact Or.inr (by simp [h, Access.mode])

private theorem not_legal_of_exclusive {s : List (Action n X)} (hl : Legal s) {p : ℕ} {x : X}
    {t t' : Fin n} {m m' : LockMode} (htt' : t ≠ t') (h : m = .exclusive ∨ m' = .exclusive)
    (hp : p ≤ s.length) (ht : HoldsBefore s t x m p) (ht' : HoldsBefore s t' x m' p) : False := by
  obtain ⟨hm, hm'⟩ := hl p hp x t t' m m' htt' ht ht'
  rcases h with h | h
  · exact absurd (hm.symm.trans h) (by decide)
  · exact absurd (hm'.symm.trans h) (by decide)

/-- **The two-phase locking theorem**: if the reads and writes of a locked schedule are distinct,
are covered by locks, and the schedule is legal and two-phase, then its reads and writes form a
conflict-serializable schedule. -/
theorem TwoPhase.conflictSerializable {s : List (Action n X)}
    (hnd : (ops s).Nodup) (hwf : LocksCover s) (hl : Legal s) (h2 : TwoPhase s) :
    ConflictSerializable (ops s) := by
  refine conflictSerializable_of_rank hnd (fun t => s.findIdx (Action.isUnlockBy t)) ?_
  rintro i j ⟨a, -, b, -, rfl, rfl, hab, hsub⟩
  obtain ⟨pa, pb, hpab, hpa, hpb⟩ := exists_lt_of_pair_sublist_ops hsub
  obtain ⟨qa, hqa, ⟨ma, hla, hma⟩, hfreea⟩ := hwf pa a hpa
  obtain ⟨qb, hqb, ⟨mb, hlb, hmb⟩, hfreeb⟩ := hwf pb b hpb
  have hitem : b.item = a.item := hab.2.1.symm
  rw [hitem] at hlb hfreeb
  have hmodes := conflict_mode hab
  rcases lt_trichotomy qa qb with hlt | heq | hgt
  · -- `a`'s lock comes first: `a.txn` must release `x` before `b.txn` acquires it.
    by_cases hrel : ∃ r, qa < r ∧ r < qb + 1 ∧ s[r]? = some (.unlock a.txn a.item)
    · obtain ⟨r, -, hr, hru⟩ := hrel
      have h1 := findIdx_le_of_getElem? (p := Action.isUnlockBy a.txn) hru
        (by simp [Action.isUnlockBy])
      have h2' := lt_findIdx_of_lock h2 hlb
      change s.findIdx (Action.isUnlockBy a.txn) < s.findIdx (Action.isUnlockBy b.txn)
      omega
    · push Not at hrel
      exfalso
      refine not_legal_of_exclusive hl hab.1 hmodes (p := qb + 1)
        (Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hlb).1)
        ⟨qa, by omega, ⟨ma, hla, hma⟩, fun r h₂ h₁ => hrel r h₁ h₂⟩
        ⟨qb, by omega, ⟨mb, hlb, hmb⟩, fun r h₂ h₁ => by omega⟩
  · subst heq
    have := hla.symm.trans hlb
    simp only [Option.some.injEq, Action.lock.injEq] at this
    exact absurd this.1 hab.1
  · -- `b`'s lock comes first: then both transactions hold the item just after `a`'s lock.
    exfalso
    refine not_legal_of_exclusive hl hab.1 hmodes (p := qa + 1)
      (Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hla).1)
      ⟨qa, by omega, ⟨ma, hla, hma⟩, fun r h₂ h₁ => by omega⟩
      ⟨qb, by omega, ⟨mb, hlb, hmb⟩, fun r h₂ h₁ => hfreeb r (by omega) h₁⟩

/-- **Strict two-phase locking theorem.** If the reads and writes of a locked schedule are
distinct, are covered by locks, and the schedule is legal and strict two-phase, then its reads and
writes form a conflict-serializable schedule. -/
theorem StrictTwoPhase.conflictSerializable {s : List (Action n X)}
    (hnd : (ops s).Nodup) (hwf : LocksCover s) (hl : Legal s) (h : StrictTwoPhase s) :
    ConflictSerializable (ops s) :=
  TwoPhase.conflictSerializable hnd hwf hl h.1

end Cslib.Databases
