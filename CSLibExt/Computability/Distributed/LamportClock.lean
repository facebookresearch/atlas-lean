/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lamport clocks
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Order.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.GetD
public import Mathlib.Order.Lex
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Finset.Card

/-!
# Lamport clocks satisfy the clock condition

Lamport's logical clocks (L. Lamport, *Time, clocks, and the ordering of events
in a distributed system*, CACM 21(7), 1978). An execution is a finite list of
events. Each event belongs to a process and may receive the message sent by an
earlier event, named by its position in the list (`Event.recvFrom`); every
event may also send a message. `WellFormed` says that every receipt names an
earlier event. The theorems below hold for every list; a receipt naming the
same or a later position is simply not a message edge, and its message lookup
contributes `0` to the clock.

* `Step` and `HappensBefore`: Lamport's happened-before relation is the
  transitive closure of process order (an earlier event of the same process)
  and message order (the send of a message before its receipt).
* `timestamps`: the clock algorithm, run over the execution. Each process keeps
  a counter; an event sets its process's counter to one more than the maximum
  of the counter and, for a receipt, the timestamp carried by the message, and
  takes the new value as its timestamp.
* `timestamp_lt_of_recv`: on a well-formed execution a receipt gets a larger
  timestamp than the send (Lamport's rule IR2), and `timestamp_lt_of_proc`: a
  later event of the same process gets a larger timestamp (IR1).
* `clock_condition`: if `a` happened before `b`, then the timestamp of `a` is
  smaller than that of `b`.

* `TotalBefore`, `totalBefore_of_happensBefore`, `totalBefore_irrefl`,
  `totalBefore_trans`, `totalBefore_total`: Lamport's total order on events
  (timestamps, ties broken by a linear order on processes) is a strict total
  order that extends happened-before.

* `happensBefore_irrefl`, `isStrictOrder_happensBefore`: happened-before is an
  irreflexive partial order (assumed by Lamport, a theorem in this model).
* `clockCondition_of_c1_c2`: any clock satisfying Lamport's conditions C1 and C2
  satisfies the clock condition.
* `ClockBefore`, `clockBefore_of_happensBefore`, `clockBefore_total`: the order
  induced by a clock system; for a clock satisfying the clock condition it is a
  strict total order extending happened-before.
* `exists_clock_of_extends`: Lamport's remark that every total order extending
  happened-before is induced by some clock system satisfying the clock condition.

The converse of the clock condition fails: concurrent events get ordered
timestamps too (see the tests). Vector clocks characterize happened-before
exactly.
-/

@[expose] public section

namespace Cslib.Distributed.LamportClock

variable {P : Type*}

/-- **Event.** An event of an execution, for a type $P$ of processes, consists of the process
in $P$ it belongs to and, if it is a receipt, a natural number: the position in the execution
of the event whose message it receives. The structure does not require that position to be
earlier than the event itself. -/
structure Event (P : Type*) where
  /-- The process the event belongs to. -/
  proc : P
  /-- The position of the sending event, for a receipt. -/
  recvFrom : Option ℕ

/-- **Well-formed executions.** An execution $e_0, \dots, e_{n-1}$ is well formed when every
receipt names an earlier event: whenever $e_j$ receives the message sent by the event at
position $i$, then $i < j$. -/
def WellFormed (tr : List (Event P)) : Prop :=
  ∀ j (ej : Event P) i, tr[j]? = some ej → ej.recvFrom = some i → i < j

/-- **One step of happened-before.** In an execution, position $i$ precedes position $j$ by one
step when $i < j$, both positions hold events, and either the two events belong to the same
process or the event at $j$ receives the message of the event at $i$. -/
def Step (tr : List (Event P)) (i j : ℕ) : Prop :=
  i < j ∧ ∃ ei ej, tr[i]? = some ei ∧ tr[j]? = some ej ∧
    (ei.proc = ej.proc ∨ ej.recvFrom = some i)

/-- **Happened-before.** Lamport's happened-before relation on the positions of an execution is
the transitive closure of one step of happened-before: $a$ happened before $b$ when there is a
chain $a = i_0, i_1, \dots, i_k = b$ with $k \ge 1$ in which each $i_m$ precedes $i_{m+1}$ by
one step. -/
def HappensBefore (tr : List (Event P)) : ℕ → ℕ → Prop :=
  Relation.TransGen (Step tr)

/-- **Happened-before goes forward in the execution.** If position $a$ happened before position
$b$ in an execution, then $a < b$. -/
theorem HappensBefore.lt {tr : List (Event P)} {a b : ℕ} (h : HappensBefore tr a b) : a < b := by
  induction h with
  | single hs => exact hs.1
  | tail _ hs ih => exact Nat.lt_trans ih hs.1

variable [DecidableEq P]

/-- **One step of the Lamport clock algorithm.** The state is a counter $c(p) \in \mathbb{N}$
for each process $p$ together with the timestamps assigned so far. An event $e$ of process
$p$ gets the timestamp $t = \max(c(p), s) + 1$, where $s$ is the timestamp already assigned
at the position that $e$ receives from; $s = 0$ if $e$ is not a receipt or if no timestamp
has been assigned at that position. The step sets $c(p)$ to $t$ and appends $t$ to the
timestamps.

The timestamps are kept in an array, for constant-time append and lookup. -/
def clockStep (st : (P → ℕ) × Array ℕ) (e : Event P) : (P → ℕ) × Array ℕ :=
  let t := max (st.1 e.proc) ((e.recvFrom.map fun i => st.2[i]?.getD 0).getD 0) + 1
  (Function.update st.1 e.proc t, st.2.push t)

/-- **Running the Lamport clock algorithm.** The clock algorithm over an execution applies one
step of the algorithm to each event in order, starting from all process counters $0$ and no
timestamps. The result is the final counters together with the timestamps assigned to the
events, in order. -/
def run (tr : List (Event P)) : (P → ℕ) × Array ℕ :=
  tr.foldl clockStep (fun _ => 0, #[])

/-- **Lamport timestamps.** The Lamport timestamps $t_0, \dots, t_{n-1}$ of an execution
$e_0, \dots, e_{n-1}$ are computed by Lamport's clock algorithm. Every process keeps a
counter, initially $0$. For $k = 0, \dots, n-1$ in turn, let $c$ be the current counter of
the process of $e_k$, and let $m = t_i$ if $e_k$ receives the message sent by the event at
position $i$ with $i < k$, and $m = 0$ otherwise. Then $t_k = \max(c, m) + 1$, and the
counter of the process of $e_k$ is set to $t_k$. -/
def timestamps (tr : List (Event P)) : List ℕ := (run tr).2.toList

theorem run_append_singleton (tr : List (Event P)) (e : Event P) :
    run (tr ++ [e]) = clockStep (run tr) e := by
  simp [run, List.foldl_append]

theorem length_timestamps (tr : List (Event P)) : (timestamps tr).length = tr.length := by
  induction tr using List.reverseRecOn with
  | nil => rfl
  | append_singleton tr e ih =>
      simp only [timestamps, run_append_singleton, clockStep, Array.toList_push,
        List.length_append, List.length_cons, List.length_nil] at ih ⊢
      omega

theorem timestamps_append_singleton (tr : List (Event P)) (e : Event P) :
    timestamps (tr ++ [e]) = timestamps tr ++
      [max ((run tr).1 e.proc)
        ((e.recvFrom.map fun i => (timestamps tr).getD i 0).getD 0) + 1] := by
  simp [timestamps, run_append_singleton, clockStep, List.getD_eq_getElem?_getD]

/-- **Appending events does not change earlier timestamps.** Let $e_0, \dots, e_{n-1}$ be an
execution, and extend it by appending further events. For every $i < n$, the Lamport timestamp
of the event at position $i$ is the same in the extended execution as in the original one. -/
theorem timestamps_append (tr rest : List (Event P)) {i : ℕ} (hi : i < tr.length) :
    (timestamps (tr ++ rest)).getD i 0 = (timestamps tr).getD i 0 := by
  induction rest using List.reverseRecOn with
  | nil => simp
  | append_singleton rest e ih =>
      rw [← List.append_assoc, timestamps_append_singleton, List.getD_append _ _ _ _
        (by rw [length_timestamps]; simp; omega)]
      exact ih

/-- **Process counters dominate their timestamps.** After the Lamport clock algorithm has run
over an execution, the counter of each process is at least the timestamp of every event of that
process in the execution. -/
theorem timestamp_le_clock (tr : List (Event P)) {i : ℕ} {ei : Event P}
    (hi : tr[i]? = some ei) : (timestamps tr).getD i 0 ≤ (run tr).1 ei.proc := by
  induction tr using List.reverseRecOn generalizing i with
  | nil => simp at hi
  | append_singleton tr e ih =>
      have hlen := length_timestamps tr
      rw [run_append_singleton, timestamps_append_singleton]
      by_cases hil : i < tr.length
      · rw [List.getElem?_append_left hil] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        simp only [clockStep]
        by_cases hp : ei.proc = e.proc
        · rw [hp, Function.update_self]
          have := ih hi
          rw [hp] at this
          simp only [timestamps] at this ⊢
          omega
        · rw [Function.update_of_ne hp]
          exact ih hi
      · have hieq : i = tr.length := by
          have := (List.getElem?_eq_some_iff.mp hi).1
          rw [List.length_append, List.length_singleton] at this
          omega
        subst hieq
        rw [List.getElem?_append_right (Nat.le_refl _)] at hi
        obtain rfl : e = ei := by simpa using hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp only [timestamps] at hlen
        simp [clockStep, hlen, timestamps]

/-- **A timestamp depends only on a prefix containing its event.** Let $e_0, \dots, e_{n-1}$ be
an execution and let $i < k \le n$. The Lamport timestamp of $e_i$ in the whole execution equals
its Lamport timestamp in the prefix $e_0, \dots, e_{k-1}$. -/
theorem timestamps_getD_take (tr : List (Event P)) {i k : ℕ} (hik : i < k) (hk : k ≤ tr.length) :
    (timestamps tr).getD i 0 = (timestamps (tr.take k)).getD i 0 := by
  have h := timestamps_append (tr.take k) (tr.drop k) (i := i) (by simp; omega)
  rwa [List.take_append_drop] at h

/-- **One step of happened-before raises the timestamp.** If position $i$ precedes position $j$
by one step of happened-before in an execution, then the Lamport timestamp of $i$ is smaller
than the Lamport timestamp of $j$. -/
theorem step_lt {tr : List (Event P)} {i j : ℕ} (h : Step tr i j) :
    (timestamps tr).getD i 0 < (timestamps tr).getD j 0 := by
  obtain ⟨hij, ei, ej, hi, hj, hrel⟩ := h
  have hjlen : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  have htake : tr.take (j + 1) = tr.take j ++ [ej] := by
    rw [List.take_add_one, hj]
    rfl
  have hpre : (tr.take j).length = j := by simp; omega
  rw [timestamps_getD_take tr (k := j + 1) (by omega) (by omega),
    timestamps_getD_take tr (i := j) (k := j + 1) (by omega) (by omega), htake,
    timestamps_append_singleton, List.getD_append _ _ _ _ (by rw [length_timestamps]; omega),
    List.getD_append_right _ _ _ _ (by rw [length_timestamps]; omega)]
  simp only [length_timestamps, hpre, Nat.sub_self, List.getD_cons_zero]
  have hi' : (tr.take j)[i]? = some ei := by rw [List.getElem?_take_of_lt hij]; exact hi
  rcases hrel with hp | hr
  · have := timestamp_le_clock (tr.take j) hi'
    rw [hp] at this
    omega
  · rw [hr]
    simp only [Option.map_some, Option.getD_some]
    omega

/-- **A receipt is stamped later than its send.** Let $e_0, \dots, e_{n-1}$ be a well-formed
execution and let $t_k$ be the Lamport timestamp of $e_k$. If $j < n$ and $e_j$ receives the
message sent by the event at position $i$, then $t_i < t_j$.

This is Lamport's clock condition C2, which his implementation rule IR2 guarantees. -/
theorem timestamp_lt_of_recv {tr : List (Event P)} (hwf : WellFormed tr) {i j : ℕ}
    {ej : Event P} (hj : tr[j]? = some ej) (hr : ej.recvFrom = some i) :
    (timestamps tr).getD i 0 < (timestamps tr).getD j 0 := by
  have hij := hwf j ej i hj hr
  have hilen : i < tr.length := by have := (List.getElem?_eq_some_iff.mp hj).1; omega
  exact step_lt ⟨hij, tr[i], ej, List.getElem?_eq_getElem hilen, hj, Or.inr hr⟩

/-- **Lamport timestamps increase along each process.** Let $e_0, \dots, e_{n-1}$ be an
execution and let $t_k$ be the Lamport timestamp of $e_k$. If $i < j < n$ and $e_i$ and $e_j$
belong to the same process, then $t_i < t_j$.

This is Lamport's clock condition C1, which his implementation rule IR1 guarantees. -/
theorem timestamp_lt_of_proc {tr : List (Event P)} {i j : ℕ} {ei ej : Event P}
    (hij : i < j) (hi : tr[i]? = some ei) (hj : tr[j]? = some ej) (hp : ei.proc = ej.proc) :
    (timestamps tr).getD i 0 < (timestamps tr).getD j 0 :=
  step_lt ⟨hij, ei, ej, hi, hj, Or.inl hp⟩

/-- **The clock condition.** In every execution, if the event at position $a$ happened before
the event at position $b$, then the Lamport timestamp of $a$ is smaller than the Lamport
timestamp of $b$ (Lamport 1978). -/
theorem clock_condition {tr : List (Event P)} {a b : ℕ} (h : HappensBefore tr a b) :
    (timestamps tr).getD a 0 < (timestamps tr).getD b 0 := by
  induction h with
  | single hs => exact step_lt hs
  | tail _ hs ih => exact Nat.lt_trans ih (step_lt hs)

/-! ## Lamport's total order -/

omit [DecidableEq P] in
/-- **Happened-before relates positions of the execution.** If position $a$ happened before
position $b$ in an execution, then the execution has an event at position $a$ and an event at
position $b$. -/
theorem HappensBefore.exists_events {tr : List (Event P)} {a b : ℕ} (h : HappensBefore tr a b) :
    (∃ ea, tr[a]? = some ea) ∧ ∃ eb, tr[b]? = some eb := by
  induction h with
  | single hs => obtain ⟨-, ea, eb, ha, hb, -⟩ := hs; exact ⟨⟨ea, ha⟩, eb, hb⟩
  | tail _ hs ih => obtain ⟨-, -, eb, -, hb, -⟩ := hs; exact ⟨ih.1, eb, hb⟩

variable [LinearOrder P]

/-- **Lamport's total order.** Fix a linear order on the processes. In an execution
$e_0, \dots, e_{n-1}$ with Lamport timestamps $t_0, \dots, t_{n-1}$, position $a$ precedes
position $b$ when $a < n$, $b < n$, and either $t_a < t_b$, or $t_a = t_b$ and the process of
$e_a$ is smaller than the process of $e_b$. -/
def TotalBefore (tr : List (Event P)) (a b : ℕ) : Prop :=
  ∃ ea eb, tr[a]? = some ea ∧ tr[b]? = some eb ∧
    toLex ((timestamps tr).getD a 0, ea.proc) < toLex ((timestamps tr).getD b 0, eb.proc)

/-- **Lamport's total order extends happened-before.** In every execution, if the event at
position $a$ happened before the event at position $b$, then position $a$ precedes position $b$
in Lamport's total order. -/
theorem totalBefore_of_happensBefore {tr : List (Event P)} {a b : ℕ}
    (h : HappensBefore tr a b) : TotalBefore tr a b := by
  obtain ⟨⟨ea, ha⟩, eb, hb⟩ := h.exists_events
  exact ⟨ea, eb, ha, hb, Prod.Lex.lt_iff.mpr (Or.inl (clock_condition h))⟩

theorem totalBefore_irrefl (tr : List (Event P)) (a : ℕ) : ¬ TotalBefore tr a a := by
  rintro ⟨ea, eb, ha, hb, hlt⟩
  rw [ha] at hb
  obtain rfl := Option.some.inj hb
  exact lt_irrefl _ hlt

theorem totalBefore_trans {tr : List (Event P)} {a b c : ℕ} (hab : TotalBefore tr a b)
    (hbc : TotalBefore tr b c) : TotalBefore tr a c := by
  obtain ⟨ea, eb, ha, hb, h1⟩ := hab
  obtain ⟨eb', ec, hb', hc, h2⟩ := hbc
  rw [hb] at hb'
  obtain rfl := Option.some.inj hb'
  exact ⟨ea, ec, ha, hc, h1.trans h2⟩

/-- **Lamport's order is total.** In every execution, for any two distinct positions $a \ne b$
that both hold events, $a$ precedes $b$ or $b$ precedes $a$ in Lamport's total order.

Two events of the same process have different timestamps (an earlier event of a process has
a smaller timestamp), so ties only occur between different processes, which the order on
processes breaks. -/
theorem totalBefore_total {tr : List (Event P)} {a b : ℕ} {ea eb : Event P}
    (ha : tr[a]? = some ea) (hb : tr[b]? = some eb) (hab : a ≠ b) :
    TotalBefore tr a b ∨ TotalBefore tr b a := by
  have hne : toLex ((timestamps tr).getD a 0, ea.proc) ≠
      toLex ((timestamps tr).getD b 0, eb.proc) := by
    intro heq
    have h1 : (timestamps tr).getD a 0 = (timestamps tr).getD b 0 := congrArg Prod.fst heq
    have h2 : ea.proc = eb.proc := congrArg Prod.snd heq
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · exact absurd h1 (timestamp_lt_of_proc hlt ha hb h2).ne
    · exact absurd h1 (timestamp_lt_of_proc hlt hb ha h2.symm).ne'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact Or.inl ⟨ea, eb, ha, hb, hlt⟩
  · exact Or.inr ⟨eb, ea, hb, ha, hlt⟩

/-! ## Happened-before is a strict partial order; clock systems -/

omit [DecidableEq P] [LinearOrder P] in
/-- **Happened-before is irreflexive.** No event happened before itself. Lamport assumes this
(1978, p. 559: "We assume that a ↛ a for any event a"); in this model of a finite execution it
is a consequence, since happened-before only goes forward in the list. -/
theorem happensBefore_irrefl (tr : List (Event P)) (a : ℕ) : ¬ HappensBefore tr a a :=
  fun h => Nat.lt_irrefl a h.lt

omit [DecidableEq P] [LinearOrder P] in
/-- **Happened-before is an irreflexive partial order** on the positions of an execution
(Lamport 1978, p. 559: "This implies that → is an irreflexive partial ordering on the set of all
events in the system"). -/
theorem isStrictOrder_happensBefore (tr : List (Event P)) :
    IsStrictOrder ℕ (HappensBefore tr) where
  irrefl := happensBefore_irrefl tr
  trans _ _ _ := Relation.TransGen.trans

omit [DecidableEq P] [LinearOrder P] in
/-- **Conditions C1 and C2 imply the clock condition** (Lamport 1978, p. 560). Let `C` assign a
number to every position of an execution. If `C` increases along each process (C1) and from the
send of a message to its receipt (C2), then `C` satisfies the clock condition: `a` happened
before `b` implies `C a < C b`. No clock algorithm is involved: this holds for every such `C`. -/
theorem clockCondition_of_c1_c2 {tr : List (Event P)} (C : ℕ → ℕ)
    (c1 : ∀ i j (ei ej : Event P), i < j → tr[i]? = some ei → tr[j]? = some ej →
      ei.proc = ej.proc → C i < C j)
    (c2 : ∀ i j (ej : Event P), i < j → tr[j]? = some ej → ej.recvFrom = some i → C i < C j)
    {a b : ℕ} (h : HappensBefore tr a b) : C a < C b := by
  have hstep : ∀ {i j}, Step tr i j → C i < C j := by
    rintro i j ⟨hij, ei, ej, hi, hj, hp | hr⟩
    · exact c1 i j ei ej hij hi hj hp
    · exact c2 i j ej hij hj hr
  induction h with
  | single hs => exact hstep hs
  | tail _ hs ih => exact ih.trans (hstep hs)

omit [DecidableEq P] in
/-- **The order induced by a clock system.** For a clock `C` assigning a number to each position,
`a` precedes `b` when `C a < C b`, or `C a = C b` and the process of `a` precedes that of `b`
(Lamport 1978, p. 561, the relation ⇒). With the Lamport timestamps as `C`, this is
`TotalBefore` (`totalBefore_eq_clockBefore`). -/
def ClockBefore (tr : List (Event P)) (C : ℕ → ℕ) (a b : ℕ) : Prop :=
  ∃ ea eb, tr[a]? = some ea ∧ tr[b]? = some eb ∧ toLex (C a, ea.proc) < toLex (C b, eb.proc)

/-- **Lamport's total order is the order induced by the Lamport timestamps.** -/
theorem totalBefore_eq_clockBefore (tr : List (Event P)) :
    TotalBefore tr = ClockBefore tr (fun a => (timestamps tr).getD a 0) :=
  rfl

omit [DecidableEq P] in
/-- **The order induced by a clock satisfying the clock condition extends happened-before.**
If a clock `C` satisfies the clock condition, then `a` happened before `b` implies that `a`
precedes `b` in the order `ClockBefore tr C` (Lamport 1978, p. 561: "if a → b then a ⇒ b", for
any system of clocks satisfying the Clock Condition). -/
theorem clockBefore_of_happensBefore {tr : List (Event P)} {C : ℕ → ℕ}
    (hC : ∀ a b, HappensBefore tr a b → C a < C b) {a b : ℕ} (h : HappensBefore tr a b) :
    ClockBefore tr C a b := by
  obtain ⟨⟨ea, ha⟩, eb, hb⟩ := h.exists_events
  exact ⟨ea, eb, ha, hb, Prod.Lex.lt_iff.mpr (Or.inl (hC a b h))⟩

omit [DecidableEq P] in
theorem clockBefore_irrefl (tr : List (Event P)) (C : ℕ → ℕ) (a : ℕ) :
    ¬ ClockBefore tr C a a := by
  rintro ⟨ea, eb, ha, hb, hlt⟩
  rw [ha] at hb
  obtain rfl := Option.some.inj hb
  exact lt_irrefl _ hlt

omit [DecidableEq P] in
theorem clockBefore_trans {tr : List (Event P)} {C : ℕ → ℕ} {a b c : ℕ}
    (hab : ClockBefore tr C a b) (hbc : ClockBefore tr C b c) : ClockBefore tr C a c := by
  obtain ⟨ea, eb, ha, hb, h1⟩ := hab
  obtain ⟨eb', ec, hb', hc, h2⟩ := hbc
  rw [hb] at hb'
  obtain rfl := Option.some.inj hb'
  exact ⟨ea, ec, ha, hc, h1.trans h2⟩

omit [DecidableEq P] in
/-- **The order induced by a clock satisfying the clock condition is total** on the events of
an execution (Lamport 1978, p. 561). Two events of the same process are related by
happened-before, so the clock condition separates them, and ties between different processes
are broken by the order on processes. -/
theorem clockBefore_total {tr : List (Event P)} {C : ℕ → ℕ}
    (hC : ∀ a b, HappensBefore tr a b → C a < C b) {a b : ℕ} {ea eb : Event P}
    (ha : tr[a]? = some ea) (hb : tr[b]? = some eb) (hab : a ≠ b) :
    ClockBefore tr C a b ∨ ClockBefore tr C b a := by
  have hne : toLex (C a, ea.proc) ≠ toLex (C b, eb.proc) := by
    intro heq
    have h1 : C a = C b := congrArg Prod.fst heq
    have h2 : ea.proc = eb.proc := congrArg Prod.snd heq
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · exact absurd h1 (hC a b (.single ⟨hlt, ea, eb, ha, hb, Or.inl h2⟩)).ne
    · exact absurd h1 (hC b a (.single ⟨hlt, eb, ea, hb, ha, Or.inl h2.symm⟩)).ne'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact Or.inl ⟨ea, eb, ha, hb, hlt⟩
  · exact Or.inr ⟨eb, ea, hb, ha, hlt⟩

omit [DecidableEq P] in
/-- **Every total order extending happened-before comes from a clock system** (Lamport 1978,
p. 561: "Given any total ordering relation ⇒ which extends →, there is a system of clocks
satisfying the Clock Condition which yields that relation"). Let `r` be a strict total order
on the positions `0, …, n - 1` of an execution of length `n` that extends happened-before. Then
some clock `C` satisfies the clock condition, and the order `ClockBefore tr C` it induces is
exactly `r` on those positions. The clock is the rank of a position in `r`, so it never ties
and the order on processes plays no role. The clock need not be produced by the algorithm
`timestamps`. -/
theorem exists_clock_of_extends {tr : List (Event P)} (r : ℕ → ℕ → Prop)
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ a b c, r a b → r b c → r a c)
    (htot : ∀ a b, a < tr.length → b < tr.length → a ≠ b → r a b ∨ r b a)
    (hext : ∀ a b, HappensBefore tr a b → r a b) :
    ∃ C : ℕ → ℕ, (∀ a b, HappensBefore tr a b → C a < C b) ∧
      ∀ a b, ClockBefore tr C a b ↔ a < tr.length ∧ b < tr.length ∧ r a b := by
  classical
  let C : ℕ → ℕ := fun a => ((Finset.range tr.length).filter (fun x => r x a)).card
  have hlt : ∀ a b, a < tr.length → r a b → C a < C b := by
    intro a b ha hab
    refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, htrans _ _ _ hx.2 hab⟩
    · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hab⟩)
      exact hirr a (Finset.mem_filter.mp this).2
  have hiff : ∀ a b, a < tr.length → b < tr.length → (C a < C b ↔ r a b) := by
    intro a b ha hb
    refine ⟨fun h => ?_, hlt a b ha⟩
    by_cases hab : a = b
    · subst hab; exact absurd h (lt_irrefl _)
    · rcases htot a b ha hb hab with h' | h'
      · exact h'
      · exact absurd (hlt b a hb h') (not_lt.mpr h.le)
  refine ⟨C, fun a b h => ?_, fun a b => ?_⟩
  · obtain ⟨⟨ea, ha⟩, -⟩ := h.exists_events
    exact hlt a b (List.getElem?_eq_some_iff.mp ha).1 (hext a b h)
  · constructor
    · rintro ⟨ea, eb, ha, hb, h⟩
      have ha' := (List.getElem?_eq_some_iff.mp ha).1
      have hb' := (List.getElem?_eq_some_iff.mp hb).1
      refine ⟨ha', hb', ?_⟩
      rcases Prod.Lex.lt_iff.mp h with h | ⟨heq, hp⟩
      · exact (hiff a b ha' hb').mp h
      · by_cases hab : a = b
        · subst hab
          rw [ha] at hb
          obtain rfl := Option.some.inj hb
          exact absurd hp (lt_irrefl _)
        · rcases htot a b ha' hb' hab with h' | h'
          · exact h'
          · exact absurd heq (hlt b a hb' h').ne'
    · rintro ⟨ha, hb, h⟩
      exact ⟨tr[a], tr[b], List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb,
        Prod.Lex.lt_iff.mpr (Or.inl (hlt a b ha h))⟩

end Cslib.Distributed.LamportClock
