/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Vector clocks
-/
module

public import CSLibExt.Computability.Distributed.LamportClock
public import Mathlib.Algebra.Order.Pi

/-!
# Vector clocks characterize happened-before

Vector clocks (C. J. Fidge, *Timestamps in message-passing systems that
preserve the partial ordering*, 1988; F. Mattern, *Virtual time and global
states of distributed systems*, 1989), over the executions of
`LamportClock.lean`. Each process keeps a vector of counters, one per process.
An event first merges, for a receipt, the vector carried by the message into
its process's vector (pointwise maximum), then increments its own entry, and
takes the result as its timestamp.

* `vectorClock_le_of_step`: one step of happened-before does not decrease any
  entry.
* `eq_or_happensBefore_of_le`: if the entry of `a`'s process in `a`'s timestamp
  is at most the same entry in `b`'s timestamp, then `a = b` or `a` happened
  before `b`.
* `happensBefore_iff_lt`: for two events of an execution, `a` happened before
  `b` exactly when the timestamp of `a` is smaller than that of `b` in the
  pointwise order.
-/

@[expose] public section

namespace Cslib.Distributed.VectorClock

open LamportClock

variable {P : Type*} [DecidableEq P]

/-- The timestamp the vector clock algorithm gives to event `e`, from the
current vectors of the processes and the timestamps assigned so far. -/
def stamp (st : (P → P → ℕ) × Array (P → ℕ)) (e : Event P) : P → ℕ :=
  let base : P → ℕ := fun q =>
    max (st.1 e.proc q) ((e.recvFrom.map fun i => (st.2[i]?.getD 0) q).getD 0)
  Function.update base e.proc (base e.proc + 1)

/-- The vector clock algorithm on one event; timestamps are accumulated in an
array, for constant-time append and lookup. -/
def clockStep (st : (P → P → ℕ) × Array (P → ℕ)) (e : Event P) :
    (P → P → ℕ) × Array (P → ℕ) :=
  (Function.update st.1 e.proc (stamp st e), st.2.push (stamp st e))

/-- The vector clock algorithm over an execution, from all vectors `0`. -/
def run (tr : List (Event P)) : (P → P → ℕ) × Array (P → ℕ) :=
  tr.foldl clockStep (fun _ => 0, #[])

/-- The vector timestamps of the events of an execution. -/
def timestamps (tr : List (Event P)) : List (P → ℕ) := (run tr).2.toList

/-- The array lookup used by the algorithm agrees with the list of
timestamps. -/
theorem run_getD (tr : List (Event P)) (i : ℕ) :
    (run tr).2[i]?.getD 0 = (timestamps tr).getD i 0 := by
  simp [timestamps, List.getD_eq_getElem?_getD]

theorem run_append_singleton (tr : List (Event P)) (e : Event P) :
    run (tr ++ [e]) = clockStep (run tr) e := by
  simp [run, List.foldl_append]

theorem timestamps_append_singleton (tr : List (Event P)) (e : Event P) :
    timestamps (tr ++ [e]) = timestamps tr ++ [stamp (run tr) e] := by
  simp [timestamps, run_append_singleton, clockStep]

theorem length_timestamps (tr : List (Event P)) : (timestamps tr).length = tr.length := by
  induction tr using List.reverseRecOn with
  | nil => rfl
  | append_singleton tr e ih =>
      rw [timestamps_append_singleton, List.length_append, ih, List.length_append]
      rfl

theorem timestamps_append (tr rest : List (Event P)) {i : ℕ} (hi : i < tr.length) :
    (timestamps (tr ++ rest)).getD i 0 = (timestamps tr).getD i 0 := by
  induction rest using List.reverseRecOn with
  | nil => simp
  | append_singleton rest e ih =>
      rw [← List.append_assoc, timestamps_append_singleton, List.getD_append _ _ _ _
        (by rw [length_timestamps]; simp; omega)]
      exact ih

theorem timestamps_getD_take (tr : List (Event P)) {i k : ℕ} (hik : i < k)
    (hk : k ≤ tr.length) :
    (timestamps tr).getD i 0 = (timestamps (tr.take k)).getD i 0 := by
  have h := timestamps_append (tr.take k) (tr.drop k) (i := i) (by simp; omega)
  rwa [List.take_append_drop] at h

/-- The timestamp of the event at position `j` is the stamp computed from the
state before it. -/
theorem timestamps_getD_eq_stamp {tr : List (Event P)} {j : ℕ} {ej : Event P}
    (hj : tr[j]? = some ej) :
    (timestamps tr).getD j 0 = stamp (run (tr.take j)) ej := by
  have hjlen : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  have htake : tr.take (j + 1) = tr.take j ++ [ej] := by
    rw [List.take_add_one, hj]
    rfl
  have hpre : (timestamps (tr.take j)).length = j := by rw [length_timestamps]; simp; omega
  rw [timestamps_getD_take tr (i := j) (k := j + 1) (by omega) (by omega), htake,
    timestamps_append_singleton, List.getD_append_right _ _ _ _ (by omega), hpre,
    Nat.sub_self]
  rfl

/-- Each process's vector dominates the timestamps of its earlier events. -/
theorem timestamp_le_vector (tr : List (Event P)) {i : ℕ} {ei : Event P}
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
          have h := ih hi
          rw [hp] at h
          intro q
          refine (h q).trans ?_
          simp only [stamp]
          by_cases hq : q = e.proc
          · subst hq
            rw [Function.update_self]
            omega
          · rw [Function.update_of_ne hq]
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
        rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
        simp [clockStep]

/-- Each process's vector is `0` or the timestamp of one of its events. -/
theorem vector_eq (tr : List (Event P)) (p : P) :
    (run tr).1 p = 0 ∨ ∃ j ej, tr[j]? = some ej ∧ ej.proc = p ∧
      (run tr).1 p = (timestamps tr).getD j 0 := by
  induction tr using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton tr e ih =>
      have hlen := length_timestamps tr
      rw [run_append_singleton, timestamps_append_singleton]
      simp only [clockStep]
      by_cases hp : p = e.proc
      · subst hp
        refine Or.inr ⟨tr.length, e, by simp, rfl, ?_⟩
        rw [Function.update_self, List.getD_append_right _ _ _ _ (by omega), hlen,
          Nat.sub_self]
        rfl
      · rw [Function.update_of_ne hp]
        rcases ih with h | ⟨j, ej, hj, hjp, hv⟩
        · exact Or.inl h
        · have hjlen : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
          refine Or.inr ⟨j, ej, by rw [List.getElem?_append_left hjlen]; exact hj, hjp, ?_⟩
          rw [List.getD_append _ _ _ _ (by omega)]
          exact hv

/-- An event's own entry is positive. -/
theorem one_le_own {tr : List (Event P)} {j : ℕ} {ej : Event P} (hj : tr[j]? = some ej) :
    1 ≤ (timestamps tr).getD j 0 ej.proc := by
  rw [timestamps_getD_eq_stamp hj]
  simp [stamp]

/-- One step of happened-before does not decrease any entry. -/
theorem vectorClock_le_of_step {tr : List (Event P)} {i j : ℕ} (h : Step tr i j) :
    (timestamps tr).getD i 0 ≤ (timestamps tr).getD j 0 := by
  obtain ⟨hij, ei, ej, hi, hj, hrel⟩ := h
  rw [timestamps_getD_eq_stamp hj, timestamps_getD_take tr (k := j) hij
    (List.getElem?_eq_some_iff.mp hj).1.le]
  have hi' : (tr.take j)[i]? = some ei := by rw [List.getElem?_take_of_lt hij]; exact hi
  have hbase : ∀ q, (timestamps (tr.take j)).getD i 0 q ≤
      max ((run (tr.take j)).1 ej.proc q)
        ((ej.recvFrom.map fun i => ((run (tr.take j)).2[i]?.getD 0) q).getD 0) := by
    intro q
    rcases hrel with hp | hr
    · have h1 : (timestamps (tr.take j)).getD i 0 q ≤ (run (tr.take j)).1 ei.proc q :=
        timestamp_le_vector (tr.take j) hi' q
      rw [hp] at h1
      exact le_max_of_le_left h1
    · rw [hr]
      simp only [Option.map_some, Option.getD_some]
      rw [run_getD]
      exact le_max_right _ _
  intro q
  simp only [stamp]
  by_cases hq : q = ej.proc
  · subst hq
    rw [Function.update_self]
    have := hbase ej.proc
    omega
  · rw [Function.update_of_ne hq]
    exact hbase q

/-- Happened-before does not decrease any entry. -/
theorem vectorClock_le_of_happensBefore {tr : List (Event P)} {a b : ℕ}
    (h : HappensBefore tr a b) : (timestamps tr).getD a 0 ≤ (timestamps tr).getD b 0 := by
  induction h with
  | single hs => exact vectorClock_le_of_step hs
  | tail _ hs ih => exact ih.trans (vectorClock_le_of_step hs)

/-- **The converse direction**: if the entry of `a`'s process in `a`'s
timestamp is at most that entry in `b`'s timestamp, then `a = b` or `a`
happened before `b`. -/
theorem eq_or_happensBefore_of_le {tr : List (Event P)} :
    ∀ (b : ℕ) {a : ℕ} {ea eb : Event P}, tr[a]? = some ea → tr[b]? = some eb →
      (timestamps tr).getD a 0 ea.proc ≤ (timestamps tr).getD b 0 ea.proc →
      a = b ∨ HappensBefore tr a b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a ea eb ha hb hle
    have hblen : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
    by_cases hp : ea.proc = eb.proc
    · rcases Nat.lt_trichotomy a b with hab | rfl | hab
      · exact Or.inr (.single ⟨hab, ea, eb, ha, hb, Or.inl hp⟩)
      · exact Or.inl rfl
      · -- `b` is an earlier event of the same process: contradiction
        exfalso
        have hb' : (tr.take a)[b]? = some eb := by rw [List.getElem?_take_of_lt hab]; exact hb
        have hmono : (timestamps (tr.take a)).getD b 0 ea.proc ≤
            (run (tr.take a)).1 eb.proc ea.proc := timestamp_le_vector (tr.take a) hb' ea.proc
        rw [← timestamps_getD_take tr hab (List.getElem?_eq_some_iff.mp ha).1.le] at hmono
        rw [timestamps_getD_eq_stamp ha] at hle
        simp only [stamp, Function.update_self] at hle
        rw [← hp] at hmono
        have hmax := le_max_left ((run (tr.take a)).1 ea.proc ea.proc)
          ((ea.recvFrom.map fun i => (run (tr.take a)).2.getD i 0 ea.proc).getD 0)
        omega
    · rw [timestamps_getD_eq_stamp hb] at hle
      simp only [stamp, Function.update_of_ne hp] at hle
      have hpos := one_le_own ha
      rcases le_max_iff.mp hle with hv | hr
      · rcases vector_eq (tr.take b) eb.proc with h0 | ⟨j, ej, hj, hjp, hv'⟩
        · rw [h0, Pi.zero_apply] at hv
          omega
        · have hjb : j < b := by
            have := (List.getElem?_eq_some_iff.mp hj).1
            rw [List.length_take] at this
            omega
          have hj' : tr[j]? = some ej := by rw [List.getElem?_take_of_lt hjb] at hj; exact hj
          rw [hv', ← timestamps_getD_take tr hjb hblen.le] at hv
          have hstep : Step tr j b := ⟨hjb, ej, eb, hj', hb, Or.inl hjp⟩
          rcases ih j hjb ha hj' hv with rfl | hab
          · exact Or.inr (.single hstep)
          · exact Or.inr (.tail hab hstep)
      · cases hrecv : eb.recvFrom with
        | none =>
            rw [hrecv, Option.map_none, Option.getD_none] at hr
            omega
        | some i =>
            rw [hrecv] at hr
            simp only [Option.map_some, Option.getD_some] at hr
            by_cases hib : i < b
            · obtain ⟨ei, hi⟩ : ∃ ei, tr[i]? = some ei :=
                ⟨tr[i], List.getElem?_eq_getElem (by omega)⟩
              rw [run_getD, ← timestamps_getD_take tr hib hblen.le] at hr
              have hstep : Step tr i b := ⟨hib, ei, eb, hi, hb, Or.inr hrecv⟩
              rcases ih i hib ha hi hr with rfl | hab
              · exact Or.inr (.single hstep)
              · exact Or.inr (.tail hab hstep)
            · have : (run (tr.take b)).2[i]?.getD 0 = 0 := by
                rw [run_getD, List.getD_eq_default]
                rw [length_timestamps]
                simp
                omega
              rw [this, Pi.zero_apply] at hr
              omega

/-- **Vector clocks characterize happened-before**: for two events of an
execution, `a` happened before `b` exactly when `a`'s timestamp is smaller than
`b`'s in the pointwise order. -/
theorem happensBefore_iff_lt {tr : List (Event P)} {a b : ℕ} (ha : a < tr.length)
    (hb : b < tr.length) :
    HappensBefore tr a b ↔ (timestamps tr).getD a 0 < (timestamps tr).getD b 0 := by
  obtain ⟨ea, hea⟩ : ∃ ea, tr[a]? = some ea := ⟨tr[a], List.getElem?_eq_getElem ha⟩
  obtain ⟨eb, heb⟩ : ∃ eb, tr[b]? = some eb := ⟨tr[b], List.getElem?_eq_getElem hb⟩
  constructor
  · intro h
    refine lt_of_le_not_ge (vectorClock_le_of_happensBefore h) fun hge => ?_
    rcases eq_or_happensBefore_of_le a heb hea (hge eb.proc) with rfl | hba
    · exact absurd h.lt (lt_irrefl _)
    · exact absurd (h.lt.trans hba.lt) (lt_irrefl _)
  · intro h
    rcases eq_or_happensBefore_of_le b hea heb (h.le ea.proc) with rfl | hab
    · exact absurd h (lt_irrefl _)
    · exact hab

end Cslib.Distributed.VectorClock
