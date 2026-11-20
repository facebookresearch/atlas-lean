/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Policy.PendingLayout
import Code.Transcription.Powerloop
import Mathlib.Data.List.Pairwise

/-!
# Pending-stack power invariants

The pending array is unbounded in the Lean model.  This module records the
PowerSort policy facts from CPython: every stored boundary label is exactly the
result of the transcribed `powerloop` on the adjacent runs' current geometry,
and powers on older runs strictly increase in C array order and lie in the
concrete interval `1 .. 60`.  There is deliberately no
`MAX_MERGE_PENDING` guard in either invariant.
-/

namespace CPythonListsort

universe u v

/-- The exact node power belonging to the boundary between two adjacent
pending runs.  `left.base - basekeys` is CPython's `s1`; the remaining
arguments are the two current run lengths and the original list length. -/
def pendingBoundaryPower (basekeys : Nat) (listlen : PySSize)
    (left right : PendingRun) : Nat :=
  powerloop (BitVec.ofNat 64 (left.base - basekeys)) left.len right.len listlen

/-- Every left endpoint of an adjacent pending-run pair stores exactly the
power computed from that pair's current geometry.  The final run has no
outgoing boundary, so its stored field is deliberately unconstrained. -/
def ExactBoundaryPowers (basekeys : Nat) (listlen : PySSize) :
    List PendingRun → Prop
  | [] => True
  | [_] => True
  | left :: right :: rest =>
      left.power = some (pendingBoundaryPower basekeys listlen left right) ∧
        ExactBoundaryPowers basekeys listlen (right :: rest)

/-- A list of pending runs has initialized, strictly increasing powers in the
concrete range produced by `powerloop`.  The witness list follows C array
order, so its head is the oldest pending run. -/
def IncreasingPendingPowers (runs : List PendingRun) : Prop :=
  ∃ powers : List Nat,
    runs.map PendingRun.power = powers.map some ∧
      (∀ power ∈ powers, 1 ≤ power ∧ power ≤ 60) ∧
      powers.Pairwise (· < ·)

/-- Steady-state PowerSort invariant, immediately after a run is pushed.

The empty stack is valid.  On every nonempty stack there is exactly one newest
run, whose stored `power` field is deliberately unconstrained because
CPython's push writes only its base and length.  Every older run's stored power
is exactly the transcribed `powerloop` result for its boundary with the next
run, lies in `1 .. 60`, and increases strictly in C array order.  Consequently
the condition is vacuous for a singleton stack. -/
def PoweredPrefix (state : MergeState κ ν) : Prop :=
  state.pending.toList = [] ∨
    ∃ olderRuns newest,
      state.pending.toList = olderRuns ++ [newest] ∧
        IncreasingPendingPowers olderRuns ∧
        ExactBoundaryPowers state.basekeys state.listlen state.pending.toList

/-- Facts about a newly discovered run before the caller's unconditional
`Array.push`.  The current pending stack still covers exactly `scanned`
entries, all of its runs are powered, and `newRun` is the adjacent nonempty
run just outside that stack.  Its stored `power` field is irrelevant, matching
the C push, which writes only base and length.  The exact-boundary predicate is
stated on the virtual post-push list, so it also pins the current top run's
stored power to the boundary with `newRun`.  No array-capacity premise is
present. -/
def ReadyToPush (state : MergeState κ ν) (scanned : Nat)
    (newRun : PendingRun) : Prop :=
  PendingLayout state scanned ∧
    IncreasingPendingPowers state.pending.toList ∧
    ExactBoundaryPowers state.basekeys state.listlen
      (state.pending.toList ++ [newRun]) ∧
    newRun.base = state.basekeys + scanned ∧
    newRun.len.Nonnegative ∧
    0 < newRun.len.toNat ∧
    scanned + newRun.len.toNat ≤ state.listlen.toNat ∧
    newRun ∉ state.pending.toList

@[simp]
theorem exactBoundaryPowers_nil (basekeys : Nat) (listlen : PySSize) :
    ExactBoundaryPowers basekeys listlen [] := by
  simp [ExactBoundaryPowers]

@[simp]
theorem exactBoundaryPowers_singleton (basekeys : Nat) (listlen : PySSize)
    (run : PendingRun) :
    ExactBoundaryPowers basekeys listlen [run] := by
  simp [ExactBoundaryPowers]

/-- The first label in a list with at least two runs is the exact power of
that first boundary. -/
theorem ExactBoundaryPowers.head {basekeys : Nat} {listlen : PySSize}
    {left right : PendingRun} {rest : List PendingRun}
    (h : ExactBoundaryPowers basekeys listlen (left :: right :: rest)) :
    left.power = some (pendingBoundaryPower basekeys listlen left right) := by
  exact h.1

/-- Dropping the oldest run preserves exact labels for every remaining
adjacent boundary. -/
theorem ExactBoundaryPowers.tail {basekeys : Nat} {listlen : PySSize}
    {head : PendingRun} {tail : List PendingRun}
    (h : ExactBoundaryPowers basekeys listlen (head :: tail)) :
    ExactBoundaryPowers basekeys listlen tail := by
  cases tail with
  | nil => simp
  | cons next rest => exact h.2

/-- Project the exact stored label at any displayed adjacent pair. -/
theorem ExactBoundaryPowers.pair_of_append {basekeys : Nat}
    {listlen : PySSize} {before after : List PendingRun}
    {left right : PendingRun}
    (h : ExactBoundaryPowers basekeys listlen
      (before ++ left :: right :: after)) :
    left.power = some (pendingBoundaryPower basekeys listlen left right) := by
  induction before with
  | nil => exact h.head
  | cons head before ih =>
      exact ih h.tail

@[simp]
theorem increasingPendingPowers_nil : IncreasingPendingPowers [] := by
  exact ⟨[], rfl, by simp, by simp⟩

theorem increasingPendingPowers_singleton_iff (run : PendingRun) :
    IncreasingPendingPowers [run] ↔
      ∃ power, run.power = some power ∧ 1 ≤ power ∧ power ≤ 60 := by
  constructor
  · rintro ⟨powers, hpowers, hrange, _⟩
    cases powers with
    | nil => simp at hpowers
    | cons power rest =>
        simp only [List.map_cons, List.cons.injEq] at hpowers
        rcases hpowers with ⟨hrun, hrest⟩
        have : rest = [] := by
          simpa using hrest
        subst rest
        exact ⟨power, hrun, (hrange power (by simp)).1,
          (hrange power (by simp)).2⟩
  · rintro ⟨power, hpower, hlower, hupper⟩
    refine ⟨[power], by simp [hpower], ?_, by simp⟩
    intro candidate hcandidate
    simp only [List.mem_singleton] at hcandidate
    subst candidate
    exact ⟨hlower, hupper⟩

/-- Every run covered by `IncreasingPendingPowers` has a concrete initialized
power in the selected range. -/
theorem IncreasingPendingPowers.run_power {runs : List PendingRun}
    (h : IncreasingPendingPowers runs) {run : PendingRun} (hrun : run ∈ runs) :
    ∃ power, run.power = some power ∧ 1 ≤ power ∧ power ≤ 60 := by
  rcases h with ⟨powers, hpowers, hrange, _⟩
  have hmapped : run.power ∈ powers.map some := by
    rw [← hpowers]
    exact List.mem_map.mpr ⟨run, hrun, rfl⟩
  rcases List.mem_map.mp hmapped with ⟨power, hpowerMem, hpower⟩
  exact ⟨power, hpower.symm, (hrange power hpowerMem).1,
    (hrange power hpowerMem).2⟩

/-- The witness powers have exactly as many entries as the runs they label. -/
theorem IncreasingPendingPowers.length_eq {runs : List PendingRun}
    (h : IncreasingPendingPowers runs) :
    ∃ powers : List Nat,
      powers.length = runs.length ∧
        (∀ power ∈ powers, 1 ≤ power ∧ power ≤ 60) ∧
        powers.Pairwise (· < ·) := by
  rcases h with ⟨powers, hpowers, hrange, hstrict⟩
  refine ⟨powers, ?_, hrange, hstrict⟩
  have := congrArg List.length hpowers
  simpa using this.symm

@[simp]
theorem poweredPrefix_empty (state : MergeState κ ν) :
    PoweredPrefix { state with pending := #[] } := by
  simp [PoweredPrefix]

@[simp]
theorem poweredPrefix_singleton (state : MergeState κ ν)
    (run : PendingRun) :
    PoweredPrefix { state with pending := #[run] } := by
  right
  exact ⟨[], run, by simp, increasingPendingPowers_nil, by simp⟩

/-- A nonempty powered-prefix state exposes its unconstrained newest run and
the increasing powered prefix before it, together with the exact labels on
all adjacent boundaries. -/
theorem PoweredPrefix.split_of_nonempty {state : MergeState κ ν}
    (h : PoweredPrefix state) (hne : state.pending.toList ≠ []) :
    ∃ olderRuns newest,
      state.pending.toList = olderRuns ++ [newest] ∧
        IncreasingPendingPowers olderRuns ∧
        ExactBoundaryPowers state.basekeys state.listlen
          state.pending.toList := by
  exact h.resolve_left hne

/-- A steady-state stack carries exact `powerloop` labels at every adjacent
boundary; the empty and singleton cases are vacuous. -/
theorem PoweredPrefix.exact_boundary_powers {state : MergeState κ ν}
    (h : PoweredPrefix state) :
    ExactBoundaryPowers state.basekeys state.listlen state.pending.toList := by
  rcases h with hempty | ⟨_, _, _, _, hexact⟩
  · simp [hempty]
  · exact hexact

/-- Project the exact `powerloop` label for any adjacent pair in a
steady-state stack. -/
theorem PoweredPrefix.boundary_power {state : MergeState κ ν}
    (h : PoweredPrefix state) {before after : List PendingRun}
    {left right : PendingRun}
    (hsplit : state.pending.toList = before ++ left :: right :: after) :
    left.power = some
      (pendingBoundaryPower state.basekeys state.listlen left right) := by
  apply ExactBoundaryPowers.pair_of_append
  rw [← hsplit]
  exact h.exact_boundary_powers

/-- In a steady-state stack, every run except the newest has a ranged,
initialized power. -/
theorem PoweredPrefix.run_power_of_mem_prefix {state : MergeState κ ν}
    (h : PoweredPrefix state) {olderRuns : List PendingRun} {newest run : PendingRun}
    (hsplit : state.pending.toList = olderRuns ++ [newest])
    (hrun : run ∈ olderRuns) :
    ∃ power, run.power = some power ∧ 1 ≤ power ∧ power ≤ 60 := by
  rcases h with hempty |
    ⟨actualOlderRuns, actualNewest, hactual, hpowers, _hexact⟩
  · rw [hempty] at hsplit
    simp at hsplit
  · have heq : olderRuns ++ [newest] = actualOlderRuns ++ [actualNewest] :=
      hsplit.symm.trans hactual
    have hlength : olderRuns.length = actualOlderRuns.length := by
      have hlengthWithTop := congrArg List.length heq
      simp only [List.length_append, List.length_singleton] at hlengthWithTop
      exact Nat.add_right_cancel hlengthWithTop
    have hparts := List.append_inj heq hlength
    rw [hparts.1] at hrun
    exact hpowers.run_power hrun

theorem ReadyToPush.layout {state : MergeState κ ν} {scanned : Nat}
    {newRun : PendingRun} (h : ReadyToPush state scanned newRun) :
    PendingLayout state scanned :=
  h.1

theorem ReadyToPush.current_powers {state : MergeState κ ν} {scanned : Nat}
    {newRun : PendingRun} (h : ReadyToPush state scanned newRun) :
    IncreasingPendingPowers state.pending.toList :=
  h.2.1

/-- Before the unconditional push, all boundaries in the virtual post-push
list already have their exact transcribed labels. -/
theorem ReadyToPush.virtual_boundary_powers {state : MergeState κ ν}
    {scanned : Nat} {newRun : PendingRun}
    (h : ReadyToPush state scanned newRun) :
    ExactBoundaryPowers state.basekeys state.listlen
      (state.pending.toList ++ [newRun]) :=
  h.2.2.1

theorem ReadyToPush.new_run_adjacent {state : MergeState κ ν} {scanned : Nat}
    {newRun : PendingRun} (h : ReadyToPush state scanned newRun) :
    newRun.base = state.basekeys + scanned :=
  h.2.2.2.1

theorem ReadyToPush.new_run_nonempty {state : MergeState κ ν} {scanned : Nat}
    {newRun : PendingRun} (h : ReadyToPush state scanned newRun) :
    newRun.len.Nonnegative ∧ 0 < newRun.len.toNat :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem ReadyToPush.new_run_within_input {state : MergeState κ ν}
    {scanned : Nat} {newRun : PendingRun} (h : ReadyToPush state scanned newRun) :
    scanned + newRun.len.toNat ≤ state.listlen.toNat :=
  h.2.2.2.2.2.2.1

theorem ReadyToPush.new_run_outside {state : MergeState κ ν}
    {scanned : Nat} {newRun : PendingRun} (h : ReadyToPush state scanned newRun) :
    newRun ∉ state.pending.toList :=
  h.2.2.2.2.2.2.2

/-- A singleton steady-state stack is valid regardless of its stale or
uninitialized stored power. -/
example (state : MergeState κ ν) (run : PendingRun) :
    PoweredPrefix { state with pending := #[run] } := by
  exact poweredPrefix_singleton state run

/-- Two unpowered runs are invalid: only the unique newest run may lack a
power. -/
example (state : MergeState κ ν) (older newest : PendingRun)
    (holder : older.power = none) (_hnewest : newest.power = none) :
    ¬PoweredPrefix { state with pending := #[older, newest] } := by
  intro h
  rcases h with hempty | ⟨olderRuns, top, hsplit, hpowers, _hexact⟩
  · simp at hempty
  · have hsplit' : [older, newest] = olderRuns ++ [top] := by simpa using hsplit
    have holderRunsLength : olderRuns.length = 1 := by
      have := congrArg List.length hsplit'
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      omega
    obtain ⟨only, rfl⟩ := List.length_eq_one_iff.mp holderRunsLength
    simp only [List.singleton_append, List.cons.injEq] at hsplit'
    have honly := hpowers.run_power (run := only) (by simp)
    rcases honly with ⟨power, hsome, _⟩
    have hsomeOlder : older.power = some power := by
      simpa [hsplit'.1] using hsome
    rw [holder] at hsomeOlder
    simp at hsomeOlder

private def mislabeledOlder : PendingRun :=
  { base := 0, len := 1, power := some 2 }

private def unlabeledNewest : PendingRun :=
  { base := 1, len := 1, power := none }

/-- On the fabricated two-run geometry, the transcribed source computes
boundary power `1`, not the stored label `2`.  This uses ordinary kernel
reduction rather than an external evaluator. -/
private theorem mislabeledBoundary_true_power :
    pendingBoundaryPower 0 (3 : PySSize) mislabeledOlder unlabeledNewest = 1 := by
  decide

/-- Regression: range and shape alone are insufficient.  The formerly
admitted fabricated stack is rejected because its first stored label is `2`
while `powerloop 0 1 1 3` returns `1`. -/
theorem fabricatedTwoRunStack_not_powered (state : MergeState κ ν) :
    ¬PoweredPrefix
      { state with
        listlen := 3
        basekeys := 0
        pending :=
          #[{ base := 0, len := 1, power := some 2 },
            { base := 1, len := 1, power := none }] } := by
  change ¬PoweredPrefix
    { state with
      listlen := 3
      basekeys := 0
      pending := #[mislabeledOlder, unlabeledNewest] }
  intro h
  have hexact := h.exact_boundary_powers
  have hlabel := hexact.head
  rw [mislabeledBoundary_true_power] at hlabel
  simp [mislabeledOlder] at hlabel

end CPythonListsort
