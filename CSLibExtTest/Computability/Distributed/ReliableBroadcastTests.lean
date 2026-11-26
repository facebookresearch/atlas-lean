/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.ReliableBroadcast
public import Mathlib.Tactic.FinCases

/-!
# Tests for reliable broadcast

Two processes, `0` and `1`, and the message `m₀` of process `0` with sequence number `0`.

* The specification: the trace in which `0` R-broadcasts `m₀` and then both processes R-deliver
  it satisfies reliable broadcast. Traces that R-deliver `m₀` twice, R-deliver it before it is
  R-broadcast, or in which only `0` R-delivers it, do not; the last does once `1` is not correct.
* A step that crashes while relaying a message does not R-deliver it.
* A fair run of the diffusion algorithm: `0` crashes while it R-broadcasts `m₀`, having sent it
  only to `1`; then `1` receives `m₀`, relays it and R-delivers it, and discards its own copy.
  The run satisfies the hypotheses of `diffusion_isReliableBroadcast`, with `1` its only correct
  process, so they are satisfiable with a crash in the middle of a broadcast. Its crashed sets
  form a failure pattern with the same correct process.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.ReliableBroadcast.Tests

open Diffusion

/-- The message of process `0` with sequence number `0`. -/
def m₀ : Message (Fin 2) Unit := ⟨0, 0, ()⟩

/-! ### The specification -/

/-- Process `0` R-broadcasts `m₀` at time `0`; processes `0` and `1` R-deliver it at times `1` and
`2`. -/
def good : ℕ → Option (Event (Fin 2) Unit)
  | 0 => some (.broadcast 0 m₀)
  | 1 => some (.deliver 0 m₀)
  | 2 => some (.deliver 1 m₀)
  | _ => none

theorem good_broadcast {t : ℕ} {p : Fin 2} {m : Message (Fin 2) Unit}
    (h : good t = some (.broadcast p m)) : t = 0 ∧ p = 0 ∧ m = m₀ := by
  rcases t with _ | _ | _ | t <;> simp_all [good]

theorem good_deliver {t : ℕ} {p : Fin 2} {m : Message (Fin 2) Unit}
    (h : good t = some (.deliver p m)) : m = m₀ ∧ (p = 0 ∧ t = 1 ∨ p = 1 ∧ t = 2) := by
  rcases t with _ | _ | _ | t <;> simp_all [good]

example : IsReliableBroadcast Set.univ good := by
  refine ⟨?_, ?_, ?_⟩
  · intro p _ m t h
    obtain ⟨rfl, rfl, rfl⟩ := good_broadcast h
    exact ⟨1, by omega, rfl⟩
  · intro p _ m t h q _
    obtain ⟨rfl, -⟩ := good_deliver h
    fin_cases q
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · intro p m t h
    obtain ⟨rfl, hpt⟩ := good_deliver h
    refine ⟨fun t' h' => ?_, 0, ?_, rfl⟩
    · obtain ⟨-, hpt'⟩ := good_deliver h'
      omega
    · omega

/-- Process `0` R-delivers `m₀` twice. -/
def twice : ℕ → Option (Event (Fin 2) Unit)
  | 0 => some (.broadcast 0 m₀)
  | 1 => some (.deliver 0 m₀)
  | 2 => some (.deliver 0 m₀)
  | _ => none

example : ¬ IsReliableBroadcast Set.univ twice := fun h => by
  have := (h.uniformIntegrity 0 m₀ 1 rfl).1 2 rfl
  omega

/-- Process `0` R-delivers `m₀` before it R-broadcasts it. -/
def early : ℕ → Option (Event (Fin 2) Unit)
  | 0 => some (.deliver 0 m₀)
  | 1 => some (.broadcast 0 m₀)
  | _ => none

example : ¬ IsReliableBroadcast Set.univ early := fun h => by
  obtain ⟨t', ht', -⟩ := (h.uniformIntegrity 0 m₀ 0 rfl).2
  omega

/-- Only process `0` R-delivers `m₀`. -/
def alone : ℕ → Option (Event (Fin 2) Unit)
  | 0 => some (.broadcast 0 m₀)
  | 1 => some (.deliver 0 m₀)
  | _ => none

example : ¬ IsReliableBroadcast Set.univ alone := fun h => by
  obtain ⟨t', ht'⟩ := h.agreement 0 trivial m₀ 1 rfl 1 trivial
  rcases t' with _ | _ | t' <;> simp [alone, m₀] at ht'

/-- If process `1` is not correct, the trace in which only `0` R-delivers `m₀` satisfies reliable
broadcast. -/
example : IsReliableBroadcast {0} alone := by
  have hb : ∀ {t p m}, alone t = some (.broadcast p m) → t = 0 ∧ p = 0 ∧ m = m₀ := by
    intro t p m h
    rcases t with _ | _ | t <;> simp_all [alone]
  have hd : ∀ {t p m}, alone t = some (.deliver p m) → t = 1 ∧ p = 0 ∧ m = m₀ := by
    intro t p m h
    rcases t with _ | _ | t <;> simp_all [alone]
  refine ⟨?_, ?_, ?_⟩
  · intro p _ m t h
    obtain ⟨rfl, rfl, rfl⟩ := hb h
    exact ⟨1, by omega, rfl⟩
  · intro p _ m t h q hq
    obtain ⟨rfl, rfl, rfl⟩ := hd h
    rw [Set.mem_singleton_iff.1 hq]
    exact ⟨1, rfl⟩
  · intro p m t h
    obtain ⟨rfl, rfl, rfl⟩ := hd h
    exact ⟨fun t' h' => (hd h').1, 0, by omega, rfl⟩

/-! ### Steps -/

example : (Step.deliver 1 0 m₀ (some ∅)).event = none := rfl

example : (Step.deliver 1 0 m₀ none).event = some (.deliver 1 m₀) := rfl

example : (Step.broadcast 0 m₀ (some ∅)).event = some (.broadcast 0 m₀) := rfl

/-! ### A run with a crash in the middle of a broadcast -/

/-- After process `0` R-broadcasts `m₀` and crashes, having sent it only to `1`. -/
def s₁ : State (Fin 2) Unit where
  crashed := insert 0 ∅
  nextSeq := Function.update (init : State (Fin 2) Unit).nextSeq 0 1
  delivered := (init : State (Fin 2) Unit).delivered
  chan := send (init : State (Fin 2) Unit).chan 0 m₀ (some {1})

/-- After process `1` receives `m₀` from `0`, relays it and R-delivers it. -/
def s₂ : State (Fin 2) Unit where
  crashed := s₁.crashed
  nextSeq := s₁.nextSeq
  delivered := Function.update s₁.delivered 1 (insert m₀ (s₁.delivered 1))
  chan := send (take s₁.chan 0 1 m₀) 1 m₀ none

/-- After process `1` discards the copy of `m₀` it sent itself. -/
def s₃ : State (Fin 2) Unit := { s₂ with chan := take s₂.chan 1 1 m₀ }

/-- The states of the run. -/
def runStates : ωSequence (State (Fin 2) Unit) :=
  ⟨fun t => match t with
    | 0 => init
    | 1 => s₁
    | 2 => s₂
    | _ => s₃⟩

/-- The steps of the run: after the three steps above, nothing happens. -/
def runSteps : ωSequence (Step (Fin 2) Unit) :=
  ⟨fun t => match t with
    | 0 => .broadcast 0 m₀ (some {1})
    | 1 => .deliver 1 0 m₀ none
    | 2 => .discard 1 1 m₀
    | _ => .idle⟩

theorem runStates_add_three (t : ℕ) : runStates (t + 3) = s₃ := rfl

theorem runSteps_add_three (t : ℕ) : runSteps (t + 3) = .idle := rfl

theorem run_execution : lts.OmegaExecution runStates runSteps := by
  intro t
  rcases t with _ | _ | _ | t
  · exact ⟨by simp [runStates, init], rfl, rfl, rfl⟩
  · refine ⟨by simp [runStates, s₁], by simp [runStates, s₁, send, init, m₀], by
      simp [runStates, s₁, init], ?_⟩
    rfl
  · refine ⟨by simp [runStates, s₂, s₁], by simp [runStates, s₂, send], by
      simp [runStates, s₂], rfl⟩
  · rw [runSteps_add_three, runStates_add_three, show t + 1 + 3 = t + 3 + 1 by omega,
      runStates_add_three]
    rfl

theorem crashed_runStates (t : ℕ) : (runStates t).crashed = if t = 0 then ∅ else {0} := by
  rcases t with _ | _ | _ | t <;> simp [runStates, init, s₁, s₂, s₃]

theorem correct_run : correct runStates = {1} := by
  ext p
  constructor
  · intro hp
    have h := hp 1
    rw [crashed_runStates] at h
    fin_cases p
    · simp at h
    · rfl
  · rintro rfl
    change ∀ t, (1 : Fin 2) ∉ (runStates t).crashed
    intro t
    rw [crashed_runStates]
    split_ifs <;> simp

theorem chan_s₃ (q p : Fin 2) : s₃.chan q p = if q = 1 ∧ p = 0 then {m₀} else 0 := by
  fin_cases q <;> fin_cases p <;> simp [s₃, s₂, s₁, take, send, init, m₀]

theorem run_reliableDelivery : ReliableDelivery runStates runSteps := by
  intro p hp q m t hm
  rw [correct_run, Set.mem_singleton_iff] at hp
  subst hp
  rcases t with _ | _ | _ | t
  · simp [runStates, init] at hm
  · have : q = 0 ∧ m = m₀ := by
      fin_cases q <;> simp_all [runStates, s₁, send, init]
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨1, by omega, by simp [runSteps, Step.Receives]⟩
  · have : q = 1 ∧ m = m₀ := by
      fin_cases q <;> simp_all [runStates, s₂, s₁, send, take, init, m₀]
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨2, le_rfl, by simp [runSteps, Step.Receives]⟩
  · rw [runStates_add_three, chan_s₃] at hm
    simp at hm

/-- The run satisfies reliable broadcast. -/
theorem run_isReliableBroadcast :
    IsReliableBroadcast (correct runStates) fun t => (runSteps t).event :=
  diffusion_isReliableBroadcast rfl run_execution run_reliableDelivery

/-- The crashed sets of the run form a failure pattern whose only correct process is `1`. -/
example : ∃ F : FailureDetector.FailurePattern (Fin 2),
    (∀ t, F.crashedBy t = (runStates t).crashed) ∧ F.correct = {1} := by
  rw [← correct_run]
  exact exists_failurePattern run_execution ⟨1, by simp [correct_run]⟩

/-- In the run, `0` R-broadcasts `m₀` and `1` R-delivers it, although `0` crashed during the
broadcast. -/
example : (runSteps 0).event = some (.broadcast 0 m₀) ∧
    (runSteps 1).event = some (.deliver 1 m₀) :=
  ⟨rfl, rfl⟩

end Cslib.Distributed.ReliableBroadcast.Tests
