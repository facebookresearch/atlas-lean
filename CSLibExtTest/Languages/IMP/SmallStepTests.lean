/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.SmallStep

@[expose] public section

namespace Cslib.IMP.SmallStepTests

def increment (name : Nat) : Cmd :=
  .assign name (.add (.var name) (.const 1))

def setThenIncrement : Cmd :=
  .seq (.assign 0 (.const 4)) (increment 0)

def countdown : Cmd :=
  .while (.not (.eq (.var 0) (.const 0)))
    (.assign 0 (.sub (.var 0) (.const 1)))

example (state : State) :
    Step (increment 0, state) (.skip, Function.update state 0 (state 0 + 1)) :=
  Step.assign state 0 (.add (.var 0) (.const 1))

example : ∃ final, Terminates setThenIncrement (fun _ => 0) final ∧ final 0 = 5 := by
  refine ⟨_, Terminates.seq (Terminates.assign _ _ _) (Terminates.assign _ _ _), ?_⟩
  simp [AExp.eval, Function.update]

example : ∃ final,
    Terminates countdown (Function.update (fun _ => 0) 0 2) final ∧ final 0 = 0 := by
  have loopStep : ∀ state : State,
      (BExp.not (.eq (.var 0) (.const 0))).eval state = true →
      Steps (countdown, state) (countdown, Function.update state 0 (state 0 - 1)) := by
    intro state hguard
    apply Relation.ReflTransGen.head (Step.whileStep _ _ _)
    apply Relation.ReflTransGen.head (Step.iteTrue hguard)
    apply Relation.ReflTransGen.head (Step.seqStep (Step.assign state 0 _))
    apply Relation.ReflTransGen.head (Step.seqSkip _ _)
    exact Relation.ReflTransGen.refl
  have exitStep : ∀ state : State,
      (BExp.not (.eq (.var 0) (.const 0))).eval state = false →
      Steps (countdown, state) (.skip, state) := by
    intro state hguard
    apply Relation.ReflTransGen.head (Step.whileStep _ _ _)
    apply Relation.ReflTransGen.head (Step.iteFalse hguard)
    exact Relation.ReflTransGen.refl
  refine ⟨_, (loopStep _ ?_).trans ((loopStep _ ?_).trans (exitStep _ ?_)), ?_⟩
  all_goals simp [BExp.eval, AExp.eval, Function.update]

#print axioms Cslib.IMP.Step.deterministic
#print axioms Cslib.IMP.Step.terminal_iff

end Cslib.IMP.SmallStepTests
