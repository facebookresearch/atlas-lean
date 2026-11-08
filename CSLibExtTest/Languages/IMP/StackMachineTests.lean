/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.StackMachine

@[expose] public section

namespace Cslib.IMP.Tests

open Cslib.IMP.StackMachine

example : compile (.assign 0 (.add (.var 0) (.const 1))) 0 =
    [Instr.load 0, Instr.push 1, Instr.add, Instr.store 0] := rfl

def stackCountdown : Cmd :=
  .while (.not (.eq (.var 0) (.const 0)))
    (.assign 0 (.sub (.var 0) (.const 1)))

example {s : State} (h : s 0 = 2) :
    ∃ pc stack s', Steps (compile stackCountdown 0) (0, [], s) (pc, stack, s') ∧
      s' 0 = 0 := by
  have hbig : BigStep stackCountdown s
      (Function.update
        (Function.update s 0 ((AExp.sub (.var 0) (.const 1)).eval s)) 0
        ((AExp.sub (.var 0) (.const 1)).eval
          (Function.update s 0 ((AExp.sub (.var 0) (.const 1)).eval s)))) := by
    show BigStep (.while (.not (.eq (.var 0) (.const 0)))
          (.assign 0 (.sub (.var 0) (.const 1)))) s _
    refine .whileTrue ?_ (.assign _ _ _) ?_
    · simp [BExp.eval, AExp.eval, h]
    · refine .whileTrue ?_ (.assign _ _ _) ?_
      · simp [BExp.eval, AExp.eval, Function.update, h]
      · refine .whileFalse ?_
        simp [BExp.eval, AExp.eval, Function.update, h]
  exact ⟨codeLength stackCountdown, [], _, compile_correct hbig, by
    simp [AExp.eval, Function.update, h]⟩

example {s : State} : ∀ y, ¬ Step (compile .skip 0) (0, [], s) y :=
  no_step_of_length_le (by simp [compile])

#print axioms Cslib.IMP.StackMachine.compile_correct

end Cslib.IMP.Tests
