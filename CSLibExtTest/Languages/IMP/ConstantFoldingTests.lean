/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for canonical constant folding
-/
module

public import CSLibExt.Languages.IMP.ConstantFolding
import all CSLibExt.Languages.IMP.ConstantFolding

/-!
# Tests for canonical constant folding

Finite checks over the public folding API: expression
folding, propagation and kill, branch merge, loop
restriction, a false-table counterexample, and the
compiler composition.
-/

namespace Cslib.IMP

/-- `3 - 5` folds to `0` in Nat. -/
theorem test_sub_trunc :
    afold emptyTable (.sub (.const 3) (.const 5)) = .const 0 :=
  rfl

/-- The folded `3 - 5` evaluates to `0`. -/
theorem test_sub_trunc_eval (s : State) :
    (afold emptyTable (.sub (.const 3) (.const 5))).eval s = 0 :=
  rfl

/-- `0 - x` folds to `0` for a concrete nonzero variable. -/
theorem test_zero_sub_var :
    afold emptyTable (.sub (.const 0) (.var 7)) = .const 0 :=
  rfl

/-- `(0 - 1) + 1` folds to `1`, not the invalid `0`. -/
theorem test_no_bad_rewrite :
    afold emptyTable
        (.add (.sub (.const 0) (.const 1)) (.const 1)) =
      .const 1 :=
  rfl

/-- `(a - b) + b` is never rewritten to `a`. -/
theorem test_no_rewrite_var :
    afold emptyTable
        (.add (.sub (.var 0) (.var 1)) (.var 1)) =
      .add (.sub (.var 0) (.var 1)) (.var 1) :=
  rfl

/-- `(0 - 1) + 1` evaluates to `1` with `a = 0`, `b = 1`. -/
theorem test_bad_identity_eval :
    (AExp.add (.sub (.var 0) (.var 1)) (.var 1)).eval
        (fun v => if v = 0 then 0 else 1) = 1 :=
  rfl

/-- Assignment uses a known constant from the table. -/
theorem test_assign_prop :
    fold (fun v => if v = 0 then some 3 else none)
        (.assign 1 (.var 0)) =
      .assign 1 (.const 3) :=
  rfl

/-- Assignment kills a stale fact about its target. -/
theorem test_assign_kill :
    fold (fun v => if v = 0 then some 3 else none)
        (.seq (.assign 0 (.var 5)) (.assign 1 (.var 0))) =
      .seq (.assign 0 (.var 5)) (.assign 1 (.var 0)) :=
  rfl

/-- Assignment installs a newly computed constant. -/
theorem test_assign_update :
    fold emptyTable
        (.seq (.assign 0 (.const 5)) (.assign 1 (.var 0))) =
      .seq (.assign 0 (.const 5)) (.assign 1 (.const 5)) :=
  rfl

/-- Branch merge keeps a fact both branches agree on. -/
theorem test_merge_agree :
    fold emptyTable
        (.seq (.ite (.truth true) (.assign 0 (.const 1))
          (.assign 0 (.const 1))) (.assign 2 (.var 0))) =
      .seq (.ite (.truth true) (.assign 0 (.const 1))
        (.assign 0 (.const 1))) (.assign 2 (.const 1)) :=
  rfl

/-- Branch merge drops facts the branches disagree on. -/
theorem test_merge_disagree :
    fold emptyTable
        (.seq (.ite (.truth true) (.assign 0 (.const 1))
          (.assign 0 (.const 2))) (.assign 2 (.var 0))) =
      .seq (.ite (.truth true) (.assign 0 (.const 1))
        (.assign 0 (.const 2))) (.assign 2 (.var 0)) :=
  rfl

/-- Loop guards ignore pre-loop facts about written variables. -/
theorem test_loop_guard :
    fold (fun v => if v = 0 then some 1 else none)
        (.while (.le (.var 0) (.const 10))
          (.assign 0 (.const 0))) =
      .while (.le (.var 0) (.const 10)) (.assign 0 (.const 0)) :=
  rfl

/-- Facts about written variables do not survive loops. -/
theorem test_loop_after :
    fold (fun v => if v = 0 then some 1 else none)
        (.seq (.while (.truth false) (.assign 0 (.const 0)))
          (.assign 2 (.var 0))) =
      .seq (.while (.truth false) (.assign 0 (.const 0)))
        (.assign 2 (.var 0)) :=
  rfl

/-- A false table makes folded and original runs disagree. -/
theorem test_false_table :
    ∃ s f1 f2,
      BigStep
        (fold (fun v => if v = 0 then some 1 else none)
          (.assign 1 (.var 0))) s f1 ∧
        BigStep (.assign 1 (.var 0)) s f2 ∧ f1 1 ≠ f2 1 := by
  refine ⟨fun _ => 0, Function.update (fun _ => 0) 1 1,
    Function.update (fun _ => 0) 1 0, ?_, ?_, ?_⟩
  · have hfold : fold (fun v => if v = 0 then some 1 else none)
          (.assign 1 (.var 0)) =
        .assign 1 (.const 1) := rfl
    rw [hfold]
    exact .assign _ _ _
  · exact .assign _ _ _
  · decide

/-- Empty-table equivalence on a concrete program. -/
theorem test_empty_equiv_concrete (s f : State) :
    BigStep
        (fold emptyTable
          (.seq (.assign 0 (.const 3))
            (.assign 1 (.add (.var 0) (.const 4))))) s f ↔
      BigStep
        (.seq (.assign 0 (.const 3))
          (.assign 1 (.add (.var 0) (.const 4)))) s f :=
  fold_equiv_empty _ s f

/-- A concrete run through the empty-table equivalence. -/
theorem test_empty_run :
    BigStep
        (fold emptyTable
          (.seq (.assign 0 (.const 3))
            (.assign 1 (.add (.var 0) (.const 4)))))
        (fun _ => 0)
        (Function.update
          (Function.update (fun _ => 0) 0 3) 1 7) := by
  apply (fold_equiv_empty _ _ _).mpr
  exact .seq (.assign _ _ _) (.assign _ _ _)

/-- Compiler composition on a concrete program, both ways. -/
theorem test_compile_comp_iff (s s' : State) :
    StackMachine.Steps
        (StackMachine.compile
          (fold emptyTable (.assign 0 (.const 5))) 0)
        (0, [], s)
        (StackMachine.codeLength
          (fold emptyTable (.assign 0 (.const 5))), [], s') ↔
      BigStep (.assign 0 (.const 5)) s s' :=
  compile_fold_correct _ s s'

/-- Compiler composition applied forward on concrete states. -/
theorem test_compile_comp_mpr :
    StackMachine.Steps
        (StackMachine.compile
          (fold emptyTable (.assign 0 (.const 5))) 0)
        (0, [], fun _ => 0)
        (StackMachine.codeLength
          (fold emptyTable (.assign 0 (.const 5))), [],
          Function.update (fun _ => 0) 0 5) := by
  apply (compile_fold_correct _ _ _).mpr
  exact .assign _ _ _

/-- Twenty skip-branch `ite`s fold without exponential blowup. -/
theorem test_ite_chain_20 :
    fold emptyTable
        (.seq (.ite (.truth true) .skip .skip)
          (.seq (.ite (.truth true) .skip .skip)
            (.seq (.ite (.truth true) .skip .skip)
              (.seq (.ite (.truth true) .skip .skip)
                (.seq (.ite (.truth true) .skip .skip)
                  (.seq (.ite (.truth true) .skip .skip)
                    (.seq (.ite (.truth true) .skip .skip)
                      (.seq (.ite (.truth true) .skip .skip)
                        (.seq (.ite (.truth true) .skip .skip)
                          (.seq (.ite (.truth true) .skip .skip)
                            (.seq (.ite (.truth true) .skip .skip)
                              (.seq (.ite (.truth true) .skip .skip)
                                (.seq (.ite (.truth true) .skip .skip)
                                  (.seq (.ite (.truth true) .skip .skip)
                                    (.seq (.ite (.truth true) .skip .skip)
                                      (.seq (.ite (.truth true) .skip .skip)
                                        (.seq (.ite (.truth true) .skip .skip)
                                          (.seq (.ite (.truth true) .skip .skip)
                                            (.seq (.ite (.truth true) .skip .skip)
                                              (.seq (.ite (.truth true) .skip .skip)
                                                (.assign 0 (.var 1)))))))))))))))))))))) =
      .seq (.ite (.truth true) .skip .skip)
        (.seq (.ite (.truth true) .skip .skip)
          (.seq (.ite (.truth true) .skip .skip)
            (.seq (.ite (.truth true) .skip .skip)
              (.seq (.ite (.truth true) .skip .skip)
                (.seq (.ite (.truth true) .skip .skip)
                  (.seq (.ite (.truth true) .skip .skip)
                    (.seq (.ite (.truth true) .skip .skip)
                      (.seq (.ite (.truth true) .skip .skip)
                        (.seq (.ite (.truth true) .skip .skip)
                          (.seq (.ite (.truth true) .skip .skip)
                            (.seq (.ite (.truth true) .skip .skip)
                              (.seq (.ite (.truth true) .skip .skip)
                                (.seq (.ite (.truth true) .skip .skip)
                                  (.seq (.ite (.truth true) .skip .skip)
                                    (.seq (.ite (.truth true) .skip .skip)
                                      (.seq (.ite (.truth true) .skip .skip)
                                        (.seq (.ite (.truth true) .skip .skip)
                                          (.seq (.ite (.truth true) .skip .skip)
                                            (.seq (.ite (.truth true) .skip .skip)
                                              (.assign 0 (.var 1))))))))))))))))))))) :=
  rfl

/-- Twenty `ite` layers each assigning on one branch, covering variables assigned on some branch at every level. -/
theorem test_ite_assigned_chain_20 :
    fold emptyTable
        (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
          (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
            (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
              (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                  (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                    (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                      (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                        (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                          (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                            (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                              (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                  (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                    (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                      (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                        (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                          (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                            (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                              (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                                (.assign 1 (.var 0)))))))))))))))))))))) =
      .seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
        (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
          (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
            (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
              (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                  (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                    (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                      (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                        (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                          (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                            (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                              (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                  (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                    (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                      (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                        (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                          (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                            (.seq (.ite (.truth true) .skip (.ite (.truth true) .skip (.assign 0 (.const 1))))
                                              (.assign 1 (.var 0))))))))))))))))))))) :=
  rfl

#print axioms test_sub_trunc
#print axioms test_sub_trunc_eval
#print axioms test_zero_sub_var
#print axioms test_no_bad_rewrite
#print axioms test_no_rewrite_var
#print axioms test_bad_identity_eval
#print axioms test_assign_prop
#print axioms test_assign_kill
#print axioms test_assign_update
#print axioms test_merge_agree
#print axioms test_merge_disagree
#print axioms test_loop_guard
#print axioms test_loop_after
#print axioms test_false_table
#print axioms test_empty_equiv_concrete
#print axioms test_empty_run
#print axioms test_compile_comp_iff
#print axioms test_compile_comp_mpr
#print axioms test_ite_chain_20
#print axioms test_ite_assigned_chain_20
#print axioms afold_eval
#print axioms bfold_eval
#print axioms fold
#print axioms fold_equiv
#print axioms fold_equiv_empty
#print axioms compile_fold_correct

end Cslib.IMP
