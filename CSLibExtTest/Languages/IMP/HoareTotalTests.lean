/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.HoareTotal

@[expose] public section

namespace Cslib.IMP.HoareTotalTests

def increment (name : Nat) : Cmd :=
  .assign name (.add (.var name) (.const 1))

def setThenIncrement : Cmd :=
  .seq (.assign 0 (.const 4)) (increment 0)

def countdown : Cmd :=
  .while (.not (.eq (.var 0) (.const 0)))
    (.assign 0 (.sub (.var 0) (.const 1)))

theorem countdown_total :
    TValid (fun _ => True) countdown (fun state => state 0 = 0) := by
  refine TValid.consequence (pre := fun _ => True) (pre' := fun _ => True)
    (post' := fun state => True ∧
      (BExp.not (.eq (.var 0) (.const 0))).eval state = false)
    (post := fun state => state 0 = 0) (command := countdown) ?_ ?_ ?_
  · exact Assertion.entails_refl _
  · refine TValid.whileVariant (invariant := fun _ => True)
      (variant := fun state => state 0) ?_
    intro state _ hguard
    have hne : state 0 ≠ 0 := by
      intro heq
      simp [heq, BExp.eval, AExp.eval] at hguard
    refine ⟨Function.update state 0
      ((AExp.sub (.var 0) (.const 1)).eval state),
      .assign state 0 _, trivial, ?_⟩
    have hvalue : (Function.update state 0
        ((AExp.sub (.var 0) (.const 1)).eval state)) 0 = state 0 - 1 := by
      simp [AExp.eval, Function.update]
    show (Function.update state 0
      ((AExp.sub (.var 0) (.const 1)).eval state)) 0 < state 0
    rw [hvalue]
    omega
  · intro state h
    rcases h with ⟨_, hguard⟩
    simp [BExp.eval, AExp.eval] at hguard
    exact of_decide_eq_true hguard

example : Valid (fun _ => True) countdown (fun state => state 0 = 0) :=
  TValid.valid countdown_total

example (state : State) :
    ∃ final, Terminates countdown state final ∧ final 0 = 0 :=
  TValid.terminates countdown_total trivial

example (state : State) :
    wp (increment 0) (fun s => s 0 = 5) state ↔ state 0 = 4 := by
  have hEq : wp (increment 0) (fun s => s 0 = 5)
      = Assertion.subst (fun s => s 0 = 5) 0 (.add (.var 0) (.const 1)) :=
    wp.assign _ _ _
  rw [hEq]
  constructor
  · intro h
    simp [Assertion.subst, AExp.eval, Function.update] at h
    omega
  · intro h
    simp [Assertion.subst, AExp.eval, Function.update, h]

theorem setThenIncrement_total :
    TValid (fun _ => True) setThenIncrement (fun state => state 0 = 5) := by
  refine wp.tvalid_iff.mpr ?_
  intro initial _
  refine ⟨Function.update (Function.update initial 0 4) 0
      ((AExp.add (.var 0) (.const 1)).eval (Function.update initial 0 4)),
    ?_, ?_⟩
  · simp only [setThenIncrement, increment]
    exact .seq (.assign initial 0 (.const 4)) (.assign _ 0 _)
  · simp [AExp.eval, Function.update]

example : Valid (fun _ => True) setThenIncrement
    (fun state => state 0 = 5) :=
  TValid.valid setThenIncrement_total

#print axioms Cslib.IMP.TValid.whileVariant
#print axioms Cslib.IMP.wp.tvalid_iff

end Cslib.IMP.HoareTotalTests
