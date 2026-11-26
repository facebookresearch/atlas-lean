/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Peripheral.OverwriteSampleRegister

/-!
# Finite histories of an overwrite-newest register

A history is a finite list of already ordered, atomic publications and destructive reads of one
slot, initially empty. A publication overwrites the slot and is numbered by its one-based position
among publications alone. Each input operation produces one tagged event, including reads of an
empty slot. The trace and final slot are computed, not supplied as hypotheses.

This is a sequential specification. It does not model timing, concurrency, or any implementation
of polling or of a driver.

## References

* H. Kopetz, *Real-Time Systems: Design Principles for Distributed Embedded Applications*,
  2nd ed., Springer, 2011, Chapter 4 (state messages with update-in-place semantics).
* N. A. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 8 (automata and traces).

The one-based numbering and destructive-read conventions follow the ATLAS article
*Reads of an overwrite-newest register return increasing publications*.
-/

@[expose] public section

namespace Cslib.Distributed.OverwriteNewestRegister

open Cslib.Semantics.Peripheral.OverwriteSampleRegister

/-- An input operation of the register, without an assigned publication number or read result. -/
inductive Operation (α : Type*) where
  /-- Overwrite the slot with the next numbered publication of `value`. -/
  | publish (value : α)
  /-- Return the current slot and then empty it. -/
  | read

/-- The published values in input order, omitting reads and retaining repeated values. -/
def publications {α : Type*} : List (Operation α) → List α :=
  List.filterMap fun
    | .publish v => some v
    | .read => none

/-- Run a finite list of atomic operations from the empty slot and zero publication count.
Return the tagged events in input order, one per operation, and the final slot. Publications use
consecutive one-based numbers independently of reads; `.read none` records an empty read. -/
def run {α : Type*} (ops : List (Operation α)) : List (Label α) × Slot α :=
  go 0 none ops
where
  /-- Return the event tags and final slot for the remaining operations, starting with `slot`
  and numbering new publications from `count + 1`. -/
  go (count : ℕ) (slot : Slot α) : List (Operation α) → List (Label α) × Slot α
    | [] => ([], slot)
    | .publish v :: ops =>
      let next := go (count + 1) (some (count + 1, v)) ops
      (.publish (count + 1) v :: next.1, next.2)
    | .read :: ops =>
      let next := go count none ops
      (.read slot :: next.1, next.2)

/-- Execution from a given slot realizes a valid trace of the register transition system. -/
private theorem run_go_valid {α : Type*} (ops : List (Operation α)) (count : ℕ) (slot : Slot α) :
    (registerLTS α).MTr slot (run.go count slot ops).1 (run.go count slot ops).2 := by
  induction ops generalizing count slot with
  | nil => exact .refl
  | cons op ops ih =>
    cases op with
    | publish v => exact .stepL (RegisterStep.publish _ _ _) (ih (count + 1) (some (count + 1, v)))
    | read => exact .stepL (RegisterStep.read _) (ih count none)

/-- The events and final slot computed by `run` form a valid trace of the overwrite-sample
register's labeled transition system starting from the empty slot. -/
theorem run_valid {α : Type*} (ops : List (Operation α)) :
    (registerLTS α).MTr none (run ops).1 (run ops).2 :=
  run_go_valid ops 0 none

/-- A publication tag identifies its value at the corresponding index in the input publications. -/
private theorem publish_mem_run_go {α : Type*} (ops : List (Operation α))
    (count : ℕ) (slot : Slot α) {n : ℕ} {v : α}
    (h : Label.publish n v ∈ (run.go count slot ops).1) :
    ∃ i, n = count + i + 1 ∧ (publications ops)[i]? = some v := by
  induction ops generalizing count slot with
  | nil => simp [run.go] at h
  | cons op ops ih =>
    cases op with
    | publish w =>
      simp only [run.go, List.mem_cons, Label.publish.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨0, rfl, rfl⟩
      · obtain ⟨i, hi, hv⟩ := ih _ _ h
        exact ⟨i + 1, by omega, hv⟩
    | read =>
      simp only [run.go, List.mem_cons, reduceCtorEq, false_or] at h
      exact ih _ _ h

/-- The publication numbers are consecutive, starting just after the given count. -/
private theorem publishIds_run_go {α : Type*} (ops : List (Operation α))
    (count : ℕ) (slot : Slot α) :
    publishIds (run.go count slot ops).1 = List.range' (count + 1) (publications ops).length := by
  induction ops generalizing count slot with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | read => exact ih count none
    | publish v =>
      change (count + 1) :: publishIds (run.go (count + 1) (some (count + 1, v)) ops).1 =
        List.range' (count + 1) ((publications ops).length + 1)
      rw [List.range'_succ, ih]

/-- A publication is either the last event and still held, immediately overwritten,
or returned by the very next event. -/
private theorem publication_next {α : Type*} (ops : List (Operation α))
    (count : ℕ) (slot : Slot α) (i n : ℕ) (v : α)
    (h : (run.go count slot ops).1[i]? = some (.publish n v)) :
    let events := (run.go count slot ops).1
    (events[i + 1]? = none ∧ (run.go count slot ops).2 = some (n, v)) ∨
      (∃ w, events[i + 1]? = some (.publish (n + 1) w)) ∨
      events[i + 1]? = some (.read (some (n, v))) := by
  induction ops generalizing count slot i with
  | nil => cases h
  | cons op ops ih =>
    cases i with
    | succ i =>
      cases op with
      | publish w => exact ih (count + 1) (some (count + 1, w)) i h
      | read => exact ih count none i h
    | zero =>
      cases op with
      | read => cases h
      | publish w =>
        change some (Label.publish (count + 1) w) = some (.publish n v) at h
        cases h
        cases ops with
        | nil => exact Or.inl ⟨rfl, rfl⟩
        | cons op ops =>
          cases op with
          | publish w => exact Or.inr (Or.inl ⟨w, rfl⟩)
          | read => exact Or.inr (Or.inr rfl)

/-- **Reads of an overwrite-newest register return increasing publications.** For any finite
input history, start with the empty slot. Each successful read returns a positive publication
number `n` and exactly the value of publication `n` (index `n - 1` in `publications`). The numbers
of successful reads are strictly increasing in trace order, so none is returned twice. If no
read returns the publication at trace index `i`, either it is the last event and is still in the
final slot, or the very next event publishes at number `n + 1`, overwriting it without a read. -/
theorem trace_correct {α : Type*} (ops : List (Operation α)) :
    let events := (run ops).1
    let slot := (run ops).2
    (∀ n v, Label.read (some (n, v)) ∈ events → 0 < n ∧ (publications ops)[n - 1]? = some v) ∧
      (readIds events).Pairwise (· < ·) ∧
      ∀ (i n : ℕ) (v : α), events[i]? = some (.publish n v) → n ∉ readIds events →
        (events[i + 1]? = none ∧ slot = some (n, v)) ∨
          ∃ w, events[i + 1]? = some (.publish (n + 1) w) := by
  dsimp only
  have hrun := run_valid ops
  refine ⟨?_, readIds_pairwise_lt _ _ hrun ?_, ?_⟩
  · intro n v h
    have hp := publish_mem_of_read_mem _ _ hrun n v h
    obtain ⟨i, hn, hv⟩ := publish_mem_run_go ops 0 none hp
    exact ⟨by omega, by rwa [show n - 1 = i by omega]⟩
  · rw [run, publishIds_run_go]
    exact List.pairwise_lt_range'
  · intro i n v hp hn
    rcases publication_next ops 0 none i n v hp with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn (List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? h, rfl⟩)).elim

end Cslib.Distributed.OverwriteNewestRegister
