/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Languages.IMP.Hoare

@[expose] public section

namespace Cslib.IMP.HoareTests

def increment (name : Nat) : Cmd :=
  .assign name (.add (.var name) (.const 1))

example : Valid (fun state => state 0 = 4) (increment 0)
    (fun state => state 0 = 5) := by
  intro initial final hvalue hstep
  simp only [increment] at hstep
  rw [BigStep.assign_iff] at hstep
  subst final
  simp [AExp.eval, Function.update, hvalue]

def setThenIncrement : Cmd :=
  .seq (.assign 0 (.const 4)) (increment 0)

example : Valid (fun _ => True) setThenIncrement (fun state => state 0 = 5) := by
  intro initial final _ hstep
  simp only [setThenIncrement] at hstep
  rw [BigStep.seq_iff] at hstep
  obtain ⟨middle, hfirst, hsecond⟩ := hstep
  rw [BigStep.assign_iff] at hfirst
  simp only [increment] at hsecond
  rw [BigStep.assign_iff] at hsecond
  subst middle
  subst final
  simp [AExp.eval, Function.update]

def countdown : Cmd :=
  .while (.not (.eq (.var 0) (.const 0)))
    (.assign 0 (.sub (.var 0) (.const 1)))

example : Valid (fun _ => True) countdown
    (fun state => state 0 = 0) := by
  refine Valid.consequence (pre := fun _ => True) (pre' := fun _ => True)
    (post' := fun state => True ∧
      (BExp.not (.eq (.var 0) (.const 0))).eval state = false)
    (post := fun state => state 0 = 0) (command := countdown) ?_ ?_ ?_
  · exact Assertion.entails_refl _
  · apply Valid.whileLoop
    intro initial final _ _
    trivial
  · intro state h
    rcases h with ⟨_, hguard⟩
    simp [BExp.eval, AExp.eval] at hguard
    exact of_decide_eq_true hguard

example (post : Assertion) :
    wlp setThenIncrement post =
      wlp (.assign 0 (.const 4)) (wlp (increment 0) post) := by
  exact wlp.seq _ _ _

example (post : Assertion) :
    wlp countdown post = fun state =>
      ((BExp.not (.eq (.var 0) (.const 0))).eval state = false → post state) ∧
      ((BExp.not (.eq (.var 0) (.const 0))).eval state = true →
        wlp (.assign 0 (.sub (.var 0) (.const 1))) (wlp countdown post) state) := by
  exact wlp.whileLoop _ _ _

#print axioms Cslib.IMP.BigStep.deterministic
#print axioms Cslib.IMP.Valid.whileLoop
#print axioms Cslib.IMP.wlp.valid_iff
#print axioms Cslib.IMP.wlp.seq
#print axioms Cslib.IMP.wlp.whileLoop
#print axioms Cslib.IMP.wlp.invariant_le_while

end Cslib.IMP.HoareTests
