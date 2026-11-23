/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.VC
public import CSLibExt.Languages.MiniImp.ReadCost
public import CSLibExt.Algorithms.Lean.Search.LowerBound

/-!
# Executable MiniImp lower-bound search

The program uses immutable array reads and total natural arithmetic. Its ghost
invariant relates the current interval to the canonical `TimeM.lowerBound.loop`;
correctness uses `TimeM.lowerBound_spec`, rather than a second sortedness proof.
Fuel bounds interpreter recursion depth, not comparisons, machine instructions,
or wall time. No heap or word-RAM adequacy is claimed.
-/

@[expose] public section

namespace CSLibExt.Languages.MiniImp.BinarySearch

open Cslib.Algorithms.Lean.TimeM

-- Decide these concrete comparisons rather than using String.ofList_injective.
@[local simp] private theorem names_ne :
    "lo" ≠ "hi" ∧ "lo" ≠ "mid" ∧ "lo" ≠ "value" ∧
    "hi" ≠ "lo" ∧ "hi" ≠ "mid" ∧ "hi" ≠ "value" ∧
    "mid" ≠ "lo" ∧ "mid" ≠ "hi" ∧ "mid" ≠ "value" ∧
    "value" ≠ "lo" ∧ "value" ≠ "hi" ∧ "value" ≠ "mid" := by decide

/-- The loop guard `lo < hi`, using MiniImp's existing comparison syntax. -/
def guard : BExp := .not (.le (.var "hi") (.var "lo"))

/-- One actual MiniImp iteration: compute midpoint, read, then narrow the
interval. -/
def body (xs : Array Nat) (key : Nat) : Stmt :=
  .seq (.assign "mid"
      (.add (.var "lo") (.div (.sub (.var "hi") (.var "lo")) (.lit 2))))
    (.seq (.read "value" xs (.var "mid"))
      (.if_ (.not (.le (.lit key) (.var "value")))
        (.assign "lo" (.add (.var "mid") (.lit 1)))
        (.assign "hi" (.var "mid"))))

/-- Bounds plus a simulation equation. The equation is established at entry,
not assumed. -/
def invariant (xs : Array Nat) (key : Nat) (s : State) : Prop :=
  ∃ (hlohi : s "lo" ≤ s "hi") (hhi : s "hi" ≤ xs.size),
    (lowerBound.loop xs key (s "lo") (s "hi") hlohi hhi).ret =
      (lowerBound xs key).ret

/-- Search loop; the annotation has no runtime effect. -/
def loop (xs : Array Nat) (key : Nat) : Stmt :=
  .while guard (invariant xs key) (body xs key)

/-- Initialize the full interval and execute the search loop. The result is
variable `lo`. -/
def program (xs : Array Nat) (key : Nat) : Stmt :=
  .seq (.assign "lo" (.lit 0))
    (.seq (.assign "hi" (.lit xs.size)) (loop xs key))

private def mid (s : State) : Nat := s "lo" + (s "hi" - s "lo") / 2

-- This is the state of one unrolled syntax body, not another search
-- implementation.
private def stepState (xs : Array Nat) (key : Nat) (s : State)
    (h : mid s < xs.size) : State :=
  let u := (s.update "mid" (mid s)).update "value" xs[mid s]
  if xs[mid s] < key then u.update "lo" (mid s + 1) else u.update "hi" (mid s)

/-- Every midpoint read is in bounds whenever the interval is valid and the
 guard holds. -/
theorem midpoint_safe (xs : Array Nat) (s : State) (hhi : s "hi" ≤ xs.size)
    (hb : beval guard s) : s "lo" + (s "hi" - s "lo") / 2 < xs.size := by
  simp only [guard, beval, evalA] at hb
  omega

private theorem body_wp (xs : Array Nat) (key : Nat) (s : State)
    (h : mid s < xs.size) (Q : State → Prop) (hQ : Q (stepState xs key s h)) :
    wp (body xs key) Q s := by
  simp only [body, wp, evalA]
  refine ⟨h, ?_⟩
  constructor
  · intro hb
    have hc : xs[mid s] < key := by
      simpa [beval, evalA, State.update, mid] using hb
    simp only [stepState, ite_eq_left hc] at hQ
    simpa [State.update, mid] using hQ
  · intro hb
    have hc : ¬ xs[mid s] < key := by
      simpa [beval, evalA, State.update, mid] using hb
    simp only [stepState, ite_eq_right hc] at hQ
    simpa [State.update, mid] using hQ

private theorem step_bounds (xs : Array Nat) (key : Nat) (s : State)
    (hhi : s "hi" ≤ xs.size) (hb : beval guard s)
    (h : mid s < xs.size) :
    let t := stepState xs key s h
    t "lo" ≤ t "hi" ∧ t "hi" ≤ xs.size ∧
      t "hi" - t "lo" < s "hi" - s "lo" := by
  simp only [guard, beval, evalA] at hb
  dsimp only
  unfold stepState
  split <;> simp only [State.update, mid, names_ne, ↓reduceIte] <;>
    refine ⟨?_, ?_, ?_⟩ <;> omega

private theorem step_reference (xs : Array Nat) (key : Nat) (s : State)
    (hlohi : s "lo" ≤ s "hi") (hhi : s "hi" ≤ xs.size) (hb : beval guard s)
    (h : mid s < xs.size) :
    let t := stepState xs key s h
    (lowerBound.loop xs key (t "lo") (t "hi")
      (step_bounds xs key s hhi hb h).1
      (step_bounds xs key s hhi hb h).2.1).ret =
      (lowerBound.loop xs key (s "lo") (s "hi") hlohi hhi).ret := by
  have hlt : s "lo" < s "hi" := by simpa [guard, beval, evalA] using hb
  dsimp only
  conv_rhs => rw [lowerBound.loop.eq_def]
  simp only [hlt, dite_true, ret_bind]
  split
  next hc =>
    have hc' : xs[mid s] < key := hc
    simp only [stepState, ite_eq_left hc']
    simp [State.update, mid]
  next hc =>
    have hc' : ¬ xs[mid s] < key := hc
    simp only [stepState, ite_eq_right hc']
    simp [State.update, mid]

/-- The concrete body VC both checks the read and preserves the simulation
invariant. -/
theorem body_vc (xs : Array Nat) (key : Nat) (s : State)
    (hI : invariant xs key s) (hb : beval guard s) :
    wp (body xs key) (invariant xs key) s := by
  obtain ⟨hlohi, hhi, heq⟩ := hI
  have hm : mid s < xs.size := midpoint_safe xs s hhi hb
  apply body_wp xs key s hm
  exact ⟨(step_bounds xs key s hhi hb hm).1,
    (step_bounds xs key s hhi hb hm).2.1,
    (step_reference xs key s hlohi hhi hb hm).trans heq⟩

private theorem exit_eq (xs : Array Nat) (key : Nat) (s : State)
    (hI : invariant xs key s) (hb : ¬ beval guard s) :
    s "lo" = (lowerBound xs key).ret := by
  obtain ⟨hlohi, hhi, heq⟩ := hI
  have hn : ¬ s "lo" < s "hi" := by simpa [guard, beval, evalA] using hb
  rw [lowerBound.loop.eq_def] at heq
  simpa [hn] using heq

/-- The invariant holds after the actual two initialization assignments. -/
theorem invariant_initial (xs : Array Nat) (key : Nat) (s : State) :
    invariant xs key ((s.update "lo" 0).update "hi" xs.size) := by
  unfold invariant
  simp only [State.update]
  simp only [show ("lo" = "hi") = False from propext (by decide), ↓reduceIte]
  exact ⟨Nat.zero_le _, Nat.le_refl _, rfl⟩

/-- The generated VC for the full concrete MiniImp program is valid in every
entry state. -/
theorem program_vc (xs : Array Nat) (key : Nat) (s : State) :
    wp (program xs key) (fun t => t "lo" = (lowerBound xs key).ret) s := by
  refine ⟨invariant_initial xs key s, ?_, ?_⟩
  · rintro t ⟨hI, hb⟩
    exact exit_eq xs key t hI hb
  · rintro t ⟨hI, hb⟩
    exact body_vc xs key t hI hb

/-- Semantic correspondence: every successful MiniImp execution returns the
canonical index. -/
theorem bigStep_eq_lowerBound {xs : Array Nat} {key : Nat} {s t : State}
    (h : BigStep (program xs key) s t) : t "lo" = (lowerBound xs key).ret :=
  wp_sound (program_vc xs key s) h

/-- Sorted inputs return the first index with value at least the key, or the
array size. This is the canonical lower-bound specification, transported
through the MiniImp semantics. -/
theorem bigStep_spec {xs : Array Nat} {key : Nat} {s t : State}
    (hs : xs.Pairwise (fun a b => a ≤ b)) (h : BigStep (program xs key) s t) :
    t "lo" ≤ xs.size ∧
      (∀ j (_hj : j < t "lo") (_hjs : j < xs.size), xs[j] < key) ∧
      (∀ j (_hj : t "lo" ≤ j) (_hjs : j < xs.size), key ≤ xs[j]) := by
  rw [bigStep_eq_lowerBound h]
  exact lowerBound_spec xs key hs

private theorem body_exec (xs : Array Nat) (key : Nat) (s : State)
    (h : mid s < xs.size) (extra : Nat) :
    exec (extra + 4) (body xs key) s = some (stepState xs key s h) := by
  have hm : s "lo" + (s "hi" - s "lo") / 2 < xs.size := h
  unfold stepState
  split
  next hc =>
    have hc' : ¬ key ≤ xs[s "lo" + (s "hi" - s "lo") / 2] := Nat.not_le.mpr hc
    simp [body, exec, evalA, beval, State.update, mid, hm, hc']
  next hc =>
    have hc' : key ≤ xs[s "lo" + (s "hi" - s "lo") / 2] := Nat.le_of_not_gt hc
    simp [body, exec, evalA, beval, State.update, mid, hm, hc']

/-- The actual interpreter terminates on every finite array from every valid
interval. The budget is interval width plus five, independent of the reference
algorithm and sortedness. -/
theorem loop_exec_success (xs : Array Nat) (key : Nat) (fuel : Nat) (s : State)
    (hlohi : s "lo" ≤ s "hi") (hhi : s "hi" ≤ xs.size)
    (hbudget : s "hi" - s "lo" + 5 ≤ fuel) :
    ∃ t, exec fuel (loop xs key) s = some t := by
  induction fuel generalizing s with
  | zero => exact False.elim (by omega)
  | succ fuel ih =>
      by_cases hb : beval guard s
      · have hm : mid s < xs.size := midpoint_safe xs s hhi hb
        obtain ⟨hl, hh, hd⟩ := step_bounds xs key s hhi hb hm
        obtain ⟨t, ht⟩ := ih (stepState xs key s hm) hl hh (by omega)
        have hf : fuel = (fuel - 4) + 4 := by
          have hlt : s "lo" < s "hi" := by
            simpa [guard, beval, evalA] using hb
          omega
        have hbody :
            exec fuel (body xs key) s = some (stepState xs key s hm) := by
          rw [hf]
          exact body_exec xs key s hm (fuel - 4)
        refine ⟨t, ?_⟩
        simpa only [loop, exec, ite_eq_left hb, hbody, Option.bind_some]
          using ht
      · exact ⟨s, by simp only [loop, exec, ite_eq_right hb]⟩

/-- Initialization plus the actual loop succeeds with the explicit linear
budget `size + 7`. -/
theorem program_exec_success (xs : Array Nat) (key : Nat) (s : State) :
    ∃ t, exec (xs.size + 7) (program xs key) s = some t := by
  let u := (s.update "lo" 0).update "hi" xs.size
  obtain ⟨t, ht⟩ := loop_exec_success xs key (xs.size + 5) u
    (by simp [u, State.update]) (by simp [u, State.update])
    (by simp [u, State.update])
  exact ⟨t, ht⟩

/-- A runnable lower-bound demonstration. Fuel uses only the input length. -/
def run (xs : Array Nat) (key : Nat) : Option Nat :=
  (exec (xs.size + 7) (program xs key) (fun _ => 0)).map (fun s => s "lo")

/-- Every input produces the canonical result through an actual successful
MiniImp execution. -/
theorem run_eq_lowerBound (xs : Array Nat) (key : Nat) :
    run xs key = some (lowerBound xs key).ret := by
  obtain ⟨t, ht⟩ := program_exec_success xs key (fun _ => 0)
  simp only [run, ht, Option.map_some]
  exact congrArg some (bigStep_eq_lowerBound (exec_sound ht))

/-- The executable demo always succeeds and satisfies the sorted lower-bound
contract. -/
theorem total_correct (xs : Array Nat) (key : Nat) (s : State)
    (hs : xs.Pairwise (fun a b => a ≤ b)) :
    ∃ t, exec (xs.size + 7) (program xs key) s = some t ∧
      BigStep (program xs key) s t ∧ t "lo" ≤ xs.size ∧
      (∀ j (_hj : j < t "lo") (_hjs : j < xs.size), xs[j] < key) ∧
      (∀ j (_hj : t "lo" ≤ j) (_hjs : j < xs.size), key ≤ xs[j]) := by
  obtain ⟨t, ht⟩ := program_exec_success xs key s
  exact ⟨t, ht, exec_sound ht, bigStep_spec hs (exec_sound ht)⟩

/-- Actual body transitions preserve the established ghost invariant. -/
theorem body_preserves {xs : Array Nat} {key : Nat} {s t : State}
    (hI : invariant xs key s) (hb : beval guard s)
    (h : BigStep (body xs key) s t) : invariant xs key t :=
  wp_sound (body_vc xs key s hI hb) h

private theorem body_reads (xs : Array Nat) (key : Nat) (s : State)
    (h : mid s < xs.size) (extra : Nat) :
    execReads (extra + 4) (body xs key) s =
      ⟨some (stepState xs key s h), 1⟩ := by
  apply Cslib.Algorithms.Lean.TimeM.ext
  · exact (execReads_ret _ _ _).trans (body_exec xs key s h extra)
  · have hm : s "lo" + (s "hi" - s "lo") / 2 < xs.size := h
    by_cases hc : xs[s "lo" + (s "hi" - s "lo") / 2] < key
    · simp [body, execReads, evalA, beval, State.update, hm, hc]
    · simp [body, execReads, evalA, beval, State.update, hm, hc]

-- One actual body read corresponds to the canonical loop's one comparison.
private theorem step_time (xs : Array Nat) (key : Nat) (s : State)
    (hlohi : s "lo" ≤ s "hi") (hhi : s "hi" ≤ xs.size) (hb : beval guard s)
    (h : mid s < xs.size) :
    let t := stepState xs key s h
    1 + (lowerBound.loop xs key (t "lo") (t "hi")
      (step_bounds xs key s hhi hb h).1
      (step_bounds xs key s hhi hb h).2.1).time =
        (lowerBound.loop xs key (s "lo") (s "hi") hlohi hhi).time := by
  have hlt : s "lo" < s "hi" := by simpa [guard, beval, evalA] using hb
  dsimp only
  conv_rhs => rw [lowerBound.loop.eq_def]
  simp only [hlt, dite_true, time_bind, time_tick]
  split
  next hc =>
    have hc' : xs[mid s] < key := hc
    simp only [stepState, ite_eq_left hc']
    simp [State.update, mid]
  next hc =>
    have hc' : ¬ xs[mid s] < key := hc
    simp only [stepState, ite_eq_right hc']
    simp [State.update, mid]

/-- At every sufficient fuel, actual loop reads equal the canonical loop's
comparison count. No sorting or assumed total-cost invariant is needed. -/
theorem loop_reads_eq_time (xs : Array Nat) (key fuel : Nat) (s : State)
    (hlohi : s "lo" ≤ s "hi") (hhi : s "hi" ≤ xs.size)
    (hbudget : s "hi" - s "lo" + 5 ≤ fuel) :
    (execReads fuel (loop xs key) s).time =
      (lowerBound.loop xs key (s "lo") (s "hi") hlohi hhi).time := by
  induction fuel generalizing s with
  | zero => exact False.elim (by omega)
  | succ fuel ih =>
      by_cases hb : beval guard s
      · have hm : mid s < xs.size := midpoint_safe xs s hhi hb
        obtain ⟨hl, hh, hd⟩ := step_bounds xs key s hhi hb hm
        have hf : fuel = (fuel - 4) + 4 := by
          have hlt : s "lo" < s "hi" := by
            simpa [guard, beval, evalA] using hb
          omega
        have hbody : execReads fuel (body xs key) s =
            ⟨some (stepState xs key s hm), 1⟩ := by
          rw [hf]
          exact body_reads xs key s hm (fuel - 4)
        simp only [loop, execReads, ite_eq_left hb, time_bind, hbody]
        change 1 + (execReads fuel (loop xs key) (stepState xs key s hm)).time
          = _
        rw [ih (stepState xs key s hm) hl hh (by omega)]
        exact step_time xs key s hlohi hhi hb hm
      · have hn : ¬ s "lo" < s "hi" := by
          simpa [guard, beval, evalA] using hb
        rw [lowerBound.loop.eq_def]
        simp only [loop, execReads, ite_eq_right hb, hn, dite_false, time_pure]

/-- Initialization is free; the program's successful reads equal canonical
lower-bound time for every fuel at least `size + 7`, on every array. -/
theorem program_reads_eq_time (xs : Array Nat) (key fuel : Nat) (s : State)
    (hbudget : xs.size + 7 ≤ fuel) :
    (execReads fuel (program xs key) s).time = (lowerBound xs key).time := by
  have hf : fuel = (fuel - 3) + 3 := by omega
  rw [hf]
  let u := (s.update "lo" 0).update "hi" xs.size
  change 0 + (0 + (execReads (fuel - 3 + 1) (loop xs key) u).time) = _
  simp only [Nat.zero_add]
  have h := loop_reads_eq_time xs key (fuel - 3 + 1) u
    (by simp [u, State.update]) (by simp [u, State.update])
    (by simpa [u, State.update] using
      show xs.size + 5 ≤ fuel - 3 + 1 by omega)
  simpa [u, State.update, lowerBound] using h

/-- The actual read count is logarithmic, by the canonical cost theorem.
This bound does not require sorted input. -/
theorem program_reads_le (xs : Array Nat) (key fuel : Nat) (s : State)
    (hbudget : xs.size + 7 ≤ fuel) :
    (execReads fuel (program xs key) s).time ≤ Nat.clog 2 (xs.size + 1) := by
  rw [program_reads_eq_time xs key fuel s hbudget]
  exact lowerBound_time_le xs key

/-- A replayable composition of execution, operational read adequacy, exact
canonical cost, logarithmic bound, generated VC, Hoare triple and sorted
result specification. `ReadSteps.erase` also supplies the original BigStep
with bounds-certified reads. Fuel depends only on the input size. -/
theorem verified_read_cost (xs : Array Nat) (key : Nat) (s : State)
    (hs : xs.Pairwise (fun a b => a ≤ b)) :
    let r := execReads (xs.size + 7) (program xs key) s
    ∃ t, r.ret = some t ∧ exec (xs.size + 7) (program xs key) s = some t ∧
      ReadSteps (program xs key) s t r.time ∧
      r.time = (lowerBound xs key).time ∧
      r.time ≤ Nat.clog 2 (xs.size + 1) ∧
      wp (program xs key) (fun u => u "lo" = (lowerBound xs key).ret) s ∧
      Hoare (fun _ => True) (program xs key)
        (fun u => u "lo" = (lowerBound xs key).ret) ∧
      t "lo" ≤ xs.size ∧
      (∀ j (_hj : j < t "lo") (_hjs : j < xs.size), xs[j] < key) ∧
      (∀ j (_hj : t "lo" ≤ j) (_hjs : j < xs.size), key ≤ xs[j]) := by
  obtain ⟨t, ht⟩ := program_exec_success xs key s
  have hr := (execReads_ret (xs.size + 7) (program xs key) s).trans ht
  exact ⟨t, hr, ht, execReads_sound hr,
    program_reads_eq_time xs key _ s (Nat.le_refl _),
    program_reads_le xs key _ s (Nat.le_refl _), program_vc xs key s,
    (fun i _ _ h => wp_sound (program_vc xs key i) h),
    bigStep_spec hs (exec_sound ht)⟩

end CSLibExt.Languages.MiniImp.BinarySearch
