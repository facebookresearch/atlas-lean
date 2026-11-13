/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.TimeFromSpace
public meta import CSLibExt.Computability.Machines.Turing.MultiTape.TimeFromSpace

/-! Actual finite machines: a two-step emitter, a zero-space infinite emitter,
and the distinction between bounded space and halting. -/

open Cslib.Turing.MultiTapeTM _root_.Turing

private def countdownTr (q : Bool) (_ : Option Bool) (_ : Fin 0 → Option Bool) :
    Action 0 Bool Bool := ⟨0, Fin.elim0, some q, if q then none else some true⟩

private def countdown : MultiTapeTM 0 Bool Bool := MultiTapeTM.ofTr false countdownTr

private def countdownRun (w : List Bool) (t : Nat) : Cfg 0 Bool Bool w :=
  (stepWith countdownTr)^[t] (Cfg.init false w)

private theorem countdown_run (w : List Bool) (t : Nat) :
    countdown.runFrom (countdown.initCfg w) t = countdownRun w t :=
  runFrom_ofTr false countdownTr _ t

private theorem countdown_halts (w : List Bool) :
    countdown.HaltsAt (countdown.initCfg w) 2 := by
  refine ⟨?_, ?_⟩
  · rw [countdown_run]
    rfl
  · intro t ht
    have ht' : t = 0 ∨ t = 1 := by omega
    rcases ht' with rfl | rfl
    · rw [countdown_run]
      change (some false : Option Bool) ≠ none
      simp
    · rw [countdown_run]
      change (some true : Option Bool) ≠ none
      simp

private def loopTr (_ : Unit) (_ : Option Bool) (_ : Fin 0 → Option Bool) :
    Action 0 Bool Unit := ⟨0, Fin.elim0, some true, some ()⟩

private def loop : MultiTapeTM 0 Bool Unit := MultiTapeTM.ofTr () loopTr

private def loopRun (w : List Bool) (t : Nat) : Cfg 0 Bool Unit w :=
  (stepWith loopTr)^[t] (Cfg.init () w)

private theorem loop_run (w : List Bool) (t : Nat) :
    loop.runFrom (loop.initCfg w) t = loopRun w t :=
  runFrom_ofTr () loopTr _ t

private theorem loop_state (w : List Bool) (t : Nat) :
    (loopRun w t).state = some () := by
  induction t with
  | zero => rfl
  | succ t ih =>
    unfold loopRun at ih ⊢
    rw [Function.iterate_succ_apply']
    simp only [stepWith, ih]
    rfl

example (w : List Bool) : countdown.RunsInSpace w 0 :=
  MultiTapeNTM.runsInSpace_zero_tapes _ _ _

example (w : List Bool) :
    2 < (w.length + 2) * storageBound Bool Bool 0 0 := by
  exact haltTime_lt_coreBound
    (fun t => by simp [MultiTapeTM.spaceUsed]) (countdown_halts w)

example (w : List Bool) :
    countdown.RunsInTime w ((w.length + 2) * storageBound Bool Bool 0 0) :=
  runsInTime_coreBound (fun t => by simp [MultiTapeTM.spaceUsed])
    ⟨2, (countdown_halts w).halted⟩

example (w : List Bool) :
    countdown.RunsInTime w ((w.length + 2) * storageBoundBase Bool Bool 0 *
      2 ^ (storageBoundExp Bool 0 * 0)) :=
  runsInTime_exponential_of_space (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)
    ⟨2, (countdown_halts w).halted⟩

example : ∃ a c : Nat, ∀ (w : List Bool) (s : Nat), countdown.RunsInSpace w s →
    (∃ t, (countdown.runFrom (countdown.initCfg w) t).Halted) →
    countdown.RunsInTime w ((w.length + 2) * a * 2 ^ (c * s)) :=
  exists_exponential_time_bound countdown

example (w : List Bool) : ¬countdown.RunsInTime w 1 := by
  intro h
  exact (countdown_halts w).not_halted (by decide) (halted_runFrom_of_runsInTime h)

example (w : List Bool) : loop.RunsInSpace w 0 :=
  MultiTapeNTM.runsInSpace_zero_tapes _ _ _

example (w : List Bool) (t : Nat) : ¬loop.RunsInTime w t := by
  intro h
  have hh := halted_runFrom_of_runsInTime h
  rw [loop_run] at hh
  change (loopRun w t).state = none at hh
  rw [loop_state] at hh
  contradiction

example (w pre : List Bool) :
    (countdown.step ((countdown.initCfg w).withOutput pre)).core =
      (countdown.step (countdown.initCfg w)).core :=
  core_step_eq_of_core_eq rfl

private def inputs : List (List Bool) := [[], [false], [true], [false, true, false]]

#guard inputs.length = 4
#guard inputs.all fun w => (countdownRun w 0).state == some false
#guard inputs.all fun w => (countdownRun w 1).state == some true
#guard inputs.all fun w => (countdownRun w 2).state == none
#guard inputs.all fun w => (countdownRun w 3).state == none
#guard inputs.all fun w => (countdownRun w 2).output == [false, true]
#guard inputs.all fun w => (countdownRun w 3).output == [false, true]
#guard inputs.all fun w => (List.range 11).all fun t =>
  (loopRun w t).state == some () && (loopRun w t).output.length == t
#guard storageBound Bool Bool 0 0 = 3
#guard storageBoundBase Bool Bool 0 = 3
#guard storageBoundExp Bool 0 = 6

#print axioms haltTime_lt_coreBound
#print axioms runsInTime_coreBound
#print axioms runsInTime_exponential_of_space
#print axioms exists_exponential_time_bound

#eval IO.println "PASS: 11 runtime guards and 9 machine/time/space proof examples"
