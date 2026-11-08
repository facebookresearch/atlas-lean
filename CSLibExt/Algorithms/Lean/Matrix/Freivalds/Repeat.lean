/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Basic
public import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Fixed-count repetition of the charged Freivalds trial

Every supplied seed runs the existing trial before its returned Boolean is
combined with the accumulated result. Later trials run after a rejection.
The cost counts the same scalar arithmetic events as the single trial.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

open Cslib.Algorithms.Lean

@[no_expose] private def repeatStep {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (accepted : Bool) (r : Fin n → ZMod 2) : TimeM (Nat × Nat) Bool := do
  let current ← freivaldsTrial A B C r
  pure (accepted && current)

/-- Run every supplied trial in order, including trials after a rejection. -/
public def freivaldsRepeat {n k : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (history : Fin k → Fin n → ZMod 2) : TimeM (Nat × Nat) Bool :=
  (List.ofFn history).foldlM (repeatStep A B C) true

@[expose] public section

private theorem repeatStep_time {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (accepted : Bool) (r : Fin n → ZMod 2) :
    (repeatStep A B C accepted r).time = (3 * n ^ 2, 3 * n ^ 2) := by
  simp [repeatStep, freivaldsTrial_time]

private theorem repeatFold_time {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (seeds : List (Fin n → ZMod 2)) (accepted : Bool) :
    (seeds.foldlM (repeatStep A B C) accepted).time =
      (3 * seeds.length * n ^ 2, 3 * seeds.length * n ^ 2) := by
  induction seeds generalizing accepted with
  | nil =>
    simp
    rfl
  | cons r seeds ih =>
    rw [List.foldlM_cons]
    simp only [TimeM.time_bind, ih]
    rw [repeatStep_time]
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, List.length_cons] <;> ring

/-- All repetitions contribute their actual trial arithmetic counts. -/
theorem freivaldsRepeat_time {n k : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (history : Fin k → Fin n → ZMod 2) :
    (freivaldsRepeat A B C history).time = (3 * k * n ^ 2, 3 * k * n ^ 2) := by
  simpa only [freivaldsRepeat, List.length_ofFn] using
    repeatFold_time A B C (List.ofFn history) true

/-- The repeated executor accepts exactly when every supplied trial accepts. -/
theorem freivaldsRepeat_accept_iff {n k : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (history : Fin k → Fin n → ZMod 2) :
    (freivaldsRepeat A B C history).ret = true ↔
      ∀ i, (freivaldsTrial A B C (history i)).ret = true := by
  have returned (seeds : List (Fin n → ZMod 2)) (accepted : Bool) :
      (seeds.foldlM (repeatStep A B C) accepted).ret =
        (accepted && seeds.all (fun r => (freivaldsTrial A B C r).ret)) := by
    induction seeds generalizing accepted with
    | nil => cases accepted <;> rfl
    | cons r seeds ih =>
      rw [List.foldlM_cons]
      simp only [TimeM.ret_bind, ih]
      cases accepted <;> simp [repeatStep]
  rw [freivaldsRepeat, returned]
  simp [List.all_eq_true, List.forall_mem_ofFn_iff]

/-- Every supplied trial accepts a correct product, including empty histories. -/
theorem freivaldsRepeat_complete {n k : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (correct : freivaldsMatrix A * freivaldsMatrix B = freivaldsMatrix C)
    (history : Fin k → Fin n → ZMod 2) :
    (freivaldsRepeat A B C history).ret = true := by
  apply (freivaldsRepeat_accept_iff A B C history).mpr
  intro i
  exact freivaldsTrial_complete A B C correct (history i)

/-- Zero trials accept every supplied product and perform no arithmetic. -/
theorem freivaldsRepeat_zero {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (history : Fin 0 → Fin n → ZMod 2) :
    freivaldsRepeat A B C history = pure true := by
  apply TimeM.ext
  · apply (freivaldsRepeat_accept_iff A B C history).mpr
    intro i
    exact Fin.elim0 i
  · change (freivaldsRepeat A B C history).time = (0, 0)
    simpa using freivaldsRepeat_time A B C history

/-- Empty matrices accept every history and perform no arithmetic. -/
theorem freivaldsRepeat_empty {k : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) 0) 0)
    (history : Fin k → Fin 0 → ZMod 2) :
    freivaldsRepeat A B C history = pure true := by
  apply TimeM.ext
  · apply freivaldsRepeat_complete A B C
    ext i j
    exact Fin.elim0 i
  · change (freivaldsRepeat A B C history).time = (0, 0)
    simpa using freivaldsRepeat_time A B C history

end

end Cslib.Algorithms.Lean.Matrix
