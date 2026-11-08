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
public import Mathlib.Data.Prod.Lex

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

The converse of the clock condition fails: concurrent events get ordered
timestamps too (see the tests). Vector clocks characterize happened-before
exactly.
-/

@[expose] public section

namespace Cslib.Distributed.LamportClock

variable {P : Type*}

/-- An event of an execution: its process, and the position of the earlier
event whose message it receives, if any. -/
structure Event (P : Type*) where
  /-- The process the event belongs to. -/
  proc : P
  /-- The position of the sending event, for a receipt. -/
  recvFrom : Option ℕ

/-- Every receipt names an earlier event. -/
def WellFormed (tr : List (Event P)) : Prop :=
  ∀ j (ej : Event P) i, tr[j]? = some ej → ej.recvFrom = some i → i < j

/-- One step of happened-before: an earlier event of the same process, or the
send of a message received by the later event. -/
def Step (tr : List (Event P)) (i j : ℕ) : Prop :=
  i < j ∧ ∃ ei ej, tr[i]? = some ei ∧ tr[j]? = some ej ∧
    (ei.proc = ej.proc ∨ ej.recvFrom = some i)

/-- Lamport's happened-before relation on the positions of an execution. -/
def HappensBefore (tr : List (Event P)) : ℕ → ℕ → Prop :=
  Relation.TransGen (Step tr)

/-- Happened-before only goes forward in the execution. -/
theorem HappensBefore.lt {tr : List (Event P)} {a b : ℕ} (h : HappensBefore tr a b) : a < b := by
  induction h with
  | single hs => exact hs.1
  | tail _ hs ih => exact Nat.lt_trans ih hs.1

variable [DecidableEq P]

/-- The clock algorithm on one event: the per-process counters and the
timestamps assigned so far (an array, for constant-time append and lookup) are
updated. -/
def clockStep (st : (P → ℕ) × Array ℕ) (e : Event P) : (P → ℕ) × Array ℕ :=
  let t := max (st.1 e.proc) ((e.recvFrom.map fun i => st.2[i]?.getD 0).getD 0) + 1
  (Function.update st.1 e.proc t, st.2.push t)

/-- The clock algorithm over an execution, from all counters `0`. -/
def run (tr : List (Event P)) : (P → ℕ) × Array ℕ :=
  tr.foldl clockStep (fun _ => 0, #[])

/-- The Lamport timestamps of the events of an execution. -/
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

/-- Timestamps of a prefix are not changed by later events. -/
theorem timestamps_append (tr rest : List (Event P)) {i : ℕ} (hi : i < tr.length) :
    (timestamps (tr ++ rest)).getD i 0 = (timestamps tr).getD i 0 := by
  induction rest using List.reverseRecOn with
  | nil => simp
  | append_singleton rest e ih =>
      rw [← List.append_assoc, timestamps_append_singleton, List.getD_append _ _ _ _
        (by rw [length_timestamps]; simp; omega)]
      exact ih

/-- Each counter is at least the timestamp of every earlier event of its
process. -/
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

/-- Timestamps are determined by the prefix up to the event. -/
theorem timestamps_getD_take (tr : List (Event P)) {i k : ℕ} (hik : i < k) (hk : k ≤ tr.length) :
    (timestamps tr).getD i 0 = (timestamps (tr.take k)).getD i 0 := by
  have h := timestamps_append (tr.take k) (tr.drop k) (i := i) (by simp; omega)
  rwa [List.take_append_drop] at h

/-- One step of happened-before raises the timestamp. -/
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

/-- Lamport's rule IR2: on a well-formed execution, a receipt gets a larger
timestamp than the send. -/
theorem timestamp_lt_of_recv {tr : List (Event P)} (hwf : WellFormed tr) {i j : ℕ}
    {ej : Event P} (hj : tr[j]? = some ej) (hr : ej.recvFrom = some i) :
    (timestamps tr).getD i 0 < (timestamps tr).getD j 0 := by
  have hij := hwf j ej i hj hr
  have hilen : i < tr.length := by have := (List.getElem?_eq_some_iff.mp hj).1; omega
  exact step_lt ⟨hij, tr[i], ej, List.getElem?_eq_getElem hilen, hj, Or.inr hr⟩

/-- Lamport's rule IR1: a later event of the same process gets a larger
timestamp. -/
theorem timestamp_lt_of_proc {tr : List (Event P)} {i j : ℕ} {ei ej : Event P}
    (hij : i < j) (hi : tr[i]? = some ei) (hj : tr[j]? = some ej) (hp : ei.proc = ej.proc) :
    (timestamps tr).getD i 0 < (timestamps tr).getD j 0 :=
  step_lt ⟨hij, ei, ej, hi, hj, Or.inl hp⟩

/-- **The clock condition** (Lamport 1978): if `a` happened before `b`, the
timestamp of `a` is smaller than the timestamp of `b`. -/
theorem clock_condition {tr : List (Event P)} {a b : ℕ} (h : HappensBefore tr a b) :
    (timestamps tr).getD a 0 < (timestamps tr).getD b 0 := by
  induction h with
  | single hs => exact step_lt hs
  | tail _ hs ih => exact Nat.lt_trans ih (step_lt hs)

/-! ## Lamport's total order -/

omit [DecidableEq P] in
/-- The endpoints of happened-before are events of the execution. -/
theorem HappensBefore.exists_events {tr : List (Event P)} {a b : ℕ} (h : HappensBefore tr a b) :
    (∃ ea, tr[a]? = some ea) ∧ ∃ eb, tr[b]? = some eb := by
  induction h with
  | single hs => obtain ⟨-, ea, eb, ha, hb, -⟩ := hs; exact ⟨⟨ea, ha⟩, eb, hb⟩
  | tail _ hs ih => obtain ⟨-, -, eb, -, hb, -⟩ := hs; exact ⟨ih.1, eb, hb⟩

variable [LinearOrder P]

/-- Lamport's total order on the events of an execution: compare timestamps,
and break ties by the order on processes. -/
def TotalBefore (tr : List (Event P)) (a b : ℕ) : Prop :=
  ∃ ea eb, tr[a]? = some ea ∧ tr[b]? = some eb ∧
    toLex ((timestamps tr).getD a 0, ea.proc) < toLex ((timestamps tr).getD b 0, eb.proc)

/-- **Lamport's total order extends happened-before.** -/
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

/-- **Lamport's order is total** on the events of an execution: two events of
the same process have different timestamps (rule IR1), so ties only occur
between different processes, which the process order breaks. -/
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

end Cslib.Distributed.LamportClock
