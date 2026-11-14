/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Machines.Turing.MultiTape.TimeFromSpace
import CSLibExt.Computability.Machines.Turing.MultiTape.TimeSpace
import Mathlib.Tactic.FinCases

/-!
# Actual machines consuming the time-from-space bounds

The inherited two-step emitter and infinite emitter keep the halting and
write-only-output hypotheses visible. A one-work-tape machine writes and clears
both cells it visits, including cell `-1`. A zero-work-tape scanner takes longer
than the storage-only bound on a literal input. All assertions are stored
private theorems; diagnostic commands belong to the external audit driver.
-/

set_option autoImplicit false

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

private theorem countdown_space (w : List Bool) : countdown.RunsInSpace w 0 :=
  MultiTapeNTM.runsInSpace_zero_tapes _ _ _

private theorem countdown_strict_core_bound (w : List Bool) :
    2 < (w.length + 2) * storageBound Bool Bool 0 0 := by
  exact haltTime_lt_coreBound
    (fun t => by simp [MultiTapeTM.spaceUsed]) (countdown_halts w)

private theorem countdown_core_time (w : List Bool) :
    countdown.RunsInTime w ((w.length + 2) * storageBound Bool Bool 0 0) :=
  runsInTime_coreBound (fun t => by simp [MultiTapeTM.spaceUsed])
    ⟨2, (countdown_halts w).halted⟩

private theorem countdown_exponential_time (w : List Bool) :
    countdown.RunsInTime w ((w.length + 2) * storageBoundBase Bool Bool 0 *
      2 ^ (storageBoundExp Bool 0 * 0)) :=
  runsInTime_exponential_of_space (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)
    ⟨2, (countdown_halts w).halted⟩

private theorem countdown_uniform_constants :
    ∃ a c : Nat, ∀ (w : List Bool) (s : Nat), countdown.RunsInSpace w s →
    (∃ t, (countdown.runFrom (countdown.initCfg w) t).Halted) →
    countdown.RunsInTime w ((w.length + 2) * a * 2 ^ (c * s)) :=
  exists_exponential_time_bound countdown

private theorem countdown_one_step_too_few (w : List Bool) :
    ¬countdown.RunsInTime w 1 := by
  intro h
  exact (countdown_halts w).not_halted (by decide) (halted_runFrom_of_runsInTime h)

private theorem loop_space (w : List Bool) : loop.RunsInSpace w 0 :=
  MultiTapeNTM.runsInSpace_zero_tapes _ _ _

private theorem loop_no_time (w : List Bool) (t : Nat) : ¬loop.RunsInTime w t := by
  intro h
  have hh := halted_runFrom_of_runsInTime h
  rw [loop_run] at hh
  change (loopRun w t).state = none at hh
  rw [loop_state] at hh
  contradiction

private theorem countdown_output_prefix_core (w pre : List Bool) :
    (countdown.step ((countdown.initCfg w).withOutput pre)).core =
      (countdown.step (countdown.initCfg w)).core :=
  core_step_eq_of_core_eq rfl

private def inputs : List (List Bool) := [[], [false], [true], [false, true, false]]

private theorem inputs_count : inputs.length = 4 := by decide

private theorem countdown_probe_initial :
    (inputs.all fun w => (countdownRun w 0).state == some false) = true := by decide

private theorem countdown_probe_one :
    (inputs.all fun w => (countdownRun w 1).state == some true) = true := by decide

private theorem countdown_probe_two :
    (inputs.all fun w => (countdownRun w 2).state == none) = true := by decide

private theorem countdown_probe_three :
    (inputs.all fun w => (countdownRun w 3).state == none) = true := by decide

private theorem countdown_probe_output_two :
    (inputs.all fun w => (countdownRun w 2).output == [false, true]) = true := by decide

private theorem countdown_probe_output_three :
    (inputs.all fun w => (countdownRun w 3).output == [false, true]) = true := by decide

private theorem loop_probe_state_and_output :
    (inputs.all fun w => (List.range 11).all fun t =>
      (loopRun w t).state == some () && (loopRun w t).output.length == t) = true := by decide

private theorem storage_bound_zero_tapes : storageBound Bool Bool 0 0 = 3 := by decide

private theorem storage_base_zero_tapes : storageBoundBase Bool Bool 0 = 3 := by decide

private theorem storage_exponent_zero_tapes : storageBoundExp Bool 0 = 6 := by decide

/-! A real work tape: write at `0`, write at `-1`, clear `0`, clear `-1`, halt. -/

private def scratchTr (q : Fin 4) (_ : Option Bool) (_ : Fin 1 → Option Bool) :
    Action 1 Bool (Fin 4) :=
  match q.val with
  | 0 => ⟨0, fun _ => (some (some true), -1), none, some 1⟩
  | 1 => ⟨0, fun _ => (some (some false), 1), none, some 2⟩
  | 2 => ⟨0, fun _ => (some none, -1), none, some 3⟩
  | _ => ⟨0, fun _ => (some none, 1), some true, none⟩

private def scratch : MultiTapeTM 1 Bool (Fin 4) := MultiTapeTM.ofTr 0 scratchTr

private def scratchRun (w : List Bool) (t : ℕ) : Cfg 1 Bool (Fin 4) w :=
  (stepWith scratchTr)^[t] (Cfg.init 0 w)

private theorem scratch_run (w : List Bool) (t : ℕ) :
    scratch.runFrom (scratch.initCfg w) t = scratchRun w t :=
  runFrom_ofTr 0 scratchTr _ t

private def scratchExpected (w : List Bool) (t : ℕ) : Cfg 1 Bool (Fin 4) w :=
  match t with
  | 0 => ⟨some 0, 1, fun _ _ => none, fun _ => 0, []⟩
  | 1 => ⟨some 1, 1, fun _ z => if z = 0 then some true else none, fun _ => -1, []⟩
  | 2 => ⟨some 2, 1,
      fun _ z => if z = -1 then some false else if z = 0 then some true else none,
      fun _ => 0, []⟩
  | 3 => ⟨some 3, 1, fun _ z => if z = -1 then some false else none, fun _ => -1, []⟩
  | _ => ⟨none, 1, fun _ _ => none, fun _ => 0, [true]⟩

private theorem scratch_configurations (w : List Bool) (n : Fin 5) :
    scratch.runFrom (scratch.initCfg w) n = scratchExpected w n := by
  rw [scratch_run]
  fin_cases n <;>
    apply Cfg.ext <;>
    simp [scratchRun, scratchExpected, Function.iterate_succ_apply', stepWith, scratchTr,
      Action.apply, Cfg.init, SignType.cast]
  all_goals
    funext i z
    by_cases h₀ : z = 0 <;> by_cases h₁ : z = -1 <;> simp_all

private theorem scratch_configuration (w : List Bool) (t : ℕ) (ht : t ≤ 4) :
    scratch.runFrom (scratch.initCfg w) t = scratchExpected w t :=
  scratch_configurations w ⟨t, by omega⟩

private theorem scratch_halts (w : List Bool) :
    scratch.HaltsAt (scratch.initCfg w) 4 := by
  refine ⟨?_, ?_⟩
  · rw [scratch_configuration w 4 (by omega)]
    rfl
  · intro t ht
    have h := scratch_configurations w (⟨t, by omega⟩ : Fin 5)
    rw [h]
    have cases_t : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases cases_t with rfl | rfl | rfl | rfl <;> simp [scratchExpected, Cfg.Halted]

private theorem scratch_one_step_too_few (w : List Bool) :
    ¬scratch.RunsInTime w 3 := by
  intro ht
  exact (scratch_halts w).not_halted (by decide) (halted_runFrom_of_runsInTime ht)

private theorem scratch_visited_at_halt (w : List Bool) :
    scratch.visitedByTapeHead (scratch.initCfg w) 4 0 = {-1, 0} := by
  ext z
  simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, rfl⟩
    rw [scratch_configurations w t]
    fin_cases t <;> simp [scratchExpected]
  · intro hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨1, by rw [scratch_configurations w (1 : Fin 5)]; rfl⟩
    · exact ⟨0, rfl⟩

private theorem scratch_exact_space (w : List Bool) :
    scratch.spaceUsed (scratch.initCfg w) 4 = 2 := by
  have h (i : Fin 1) : scratch.visitedByTapeHead (scratch.initCfg w) 4 i = {-1, 0} := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact scratch_visited_at_halt w
  simp only [MultiTapeTM.spaceUsed, MultiTapeTM.spaceUsedByTape, h]
  decide

private theorem scratch_prefix_space (w : List Bool) (t : ℕ) :
    scratch.spaceUsed (scratch.initCfg w) t ≤ 2 := by
  rcases le_total t 4 with ht | ht
  · exact (MultiTapeTM.spaceUsed_mono scratch _ ht).trans_eq (scratch_exact_space w)
  · rw [MultiTapeTM.spaceUsed_eq_of_halt _ ht (scratch_halts w).halted,
      scratch_exact_space]

private theorem scratch_space (w : List Bool) : scratch.RunsInSpace w 2 := by
  intro p
  rw [p.eq_ofDeterministic]
  exact scratch_prefix_space w p.time

private theorem scratch_uses_negative_cell (w : List Bool) :
    (scratch.runFrom (scratch.initCfg w) 1).workTapePos 0 = -1 ∧
    (scratch.runFrom (scratch.initCfg w) 2).workTapes 0 (-1) = some false ∧
    (scratch.runFrom (scratch.initCfg w) 2).workTapes 0 0 = some true ∧
    (scratch.runFrom (scratch.initCfg w) 4).workTapes = fun _ _ => none := by
  rw [scratch_configuration w 1 (by omega), scratch_configuration w 2 (by omega),
    scratch_configuration w 4 (by omega)]
  simp [scratchExpected]

private theorem scratch_core_time_and_output (w : List Bool) :
    scratch.RunsInTime w ((w.length + 2) * storageBound Bool (Fin 4) 1 2) ∧
    (scratch.runFrom (scratch.initCfg w)
      ((w.length + 2) * storageBound Bool (Fin 4) 1 2)).output = [true] := by
  have ht := runsInTime_coreBound (scratch_prefix_space w) ⟨4, (scratch_halts w).halted⟩
  refine ⟨ht, (computes_iff_output_of_runsInTime ht).mp ⟨4, (scratch_halts w).halted, ?_⟩⟩
  rw [scratch_configuration w 4 (by omega)]
  rfl

private theorem scratch_exponential_time (w : List Bool) :
    scratch.RunsInTime w ((w.length + 2) * storageBoundBase Bool (Fin 4) 1 *
      2 ^ (storageBoundExp Bool 1 * 2)) :=
  runsInTime_exponential_of_space (scratch_space w) ⟨4, (scratch_halts w).halted⟩

/-! The input factor is necessary even with zero work tapes and one live state. -/

private def scanTr (_ : Unit) (a : Option Bool) (_ : Fin 0 → Option Bool) :
    Action 0 Bool Unit :=
  match a with
  | some _ => ⟨1, Fin.elim0, none, some ()⟩
  | none => ⟨0, Fin.elim0, some true, none⟩

private def scanner : MultiTapeTM 0 Bool Unit := MultiTapeTM.ofTr () scanTr

private def scanCfg (w : List Bool) (t : ℕ) (ht : t ≤ w.length) : Cfg 0 Bool Unit w :=
  ⟨some (), ⟨t + 1, by omega⟩, Fin.elim0, Fin.elim0, []⟩

private theorem scanner_prefix (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    scanner.runFrom (scanner.initCfg w) t = scanCfg w t ht := by
  induction t with
  | zero =>
    change Cfg.init () w = scanCfg w 0 ht
    apply Cfg.ext_zero_tapes <;> simp [scanCfg]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ, ih (by omega)]
    rw [show scanner.step (scanCfg w t (by omega)) =
      stepWith scanTr (scanCfg w t (by omega)) from step_ofTr () scanTr _]
    have hs : (scanCfg w t (by omega)).inputSymbol = some w[t] :=
      inputSymbolInner t (by simp [scanCfg]; omega) (by omega)
    change (scanTr () (scanCfg w t (by omega)).inputSymbol _).apply _ = _
    rw [hs]
    apply Cfg.ext_zero_tapes
    · rfl
    · change moveInputPos (scanCfg w t (by omega)).inputPos .pos = _
      rw [moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)]
      rfl
    · rfl

private theorem scanner_complete (w : List Bool) :
    scanner.runFrom (scanner.initCfg w) (w.length + 1) =
      ⟨none, ⟨w.length + 1, by omega⟩, Fin.elim0, Fin.elim0, [true]⟩ := by
  rw [MultiTapeTM.runFrom_succ, scanner_prefix w w.length le_rfl]
  rw [show scanner.step (scanCfg w w.length le_rfl) =
    stepWith scanTr (scanCfg w w.length le_rfl) from step_ofTr () scanTr _]
  have hs : (scanCfg w w.length le_rfl).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr rfl)
  change (scanTr () (scanCfg w w.length le_rfl).inputSymbol _).apply _ = _
  rw [hs]
  apply Cfg.ext_zero_tapes <;> simp [scanCfg, scanTr, Action.apply]

private theorem scanner_halts (w : List Bool) :
    scanner.HaltsAt (scanner.initCfg w) (w.length + 1) := by
  refine ⟨?_, fun t ht => ?_⟩
  · rw [scanner_complete]
  · rw [scanner_prefix w t (by omega)]
    simp [scanCfg, Cfg.Halted]

private theorem scanner_decides : Decides scanner Set.univ := by
  intro w
  refine ⟨w.length + 1, (scanner_halts w).halted, ?_⟩
  rw [scanner_complete]
  simp [MultiTapeTM.indicator]

private theorem scanner_space (w : List Bool) : scanner.RunsInSpace w 0 :=
  MultiTapeNTM.runsInSpace_zero_tapes _ _ _

private theorem scanner_literal_configuration :
    scanner.runFrom (scanner.initCfg [true, false, true, false, true, false]) 7 =
      ⟨none, 7, Fin.elim0, Fin.elim0, [true]⟩ :=
  scanner_complete _

private theorem scanner_storage_only_too_small :
    storageBound Bool Unit 0 0 < 7 ∧
    ¬scanner.RunsInTime [true, false, true, false, true, false]
      (storageBound Bool Unit 0 0) := by
  have hb : storageBound Bool Unit 0 0 = 2 := by decide
  refine ⟨by omega, fun ht => ?_⟩
  exact (scanner_halts [true, false, true, false, true, false]).not_halted
    (by simp [hb]) (halted_runFrom_of_runsInTime ht)

private theorem scanner_one_step_too_few :
    ¬scanner.RunsInTime [true, false, true, false, true, false] 6 := by
  intro ht
  exact (scanner_halts [true, false, true, false, true, false]).not_halted
    (by decide) (halted_runFrom_of_runsInTime ht)

private theorem scanner_with_input_factor (w : List Bool) :
    scanner.RunsInTime w ((w.length + 2) * storageBound Bool Unit 0 0) :=
  runsInTime_coreBound (fun t => by simp [MultiTapeTM.spaceUsed])
    ⟨w.length + 1, (scanner_halts w).halted⟩
